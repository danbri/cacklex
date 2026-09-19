// shex-behaviours: ShEx shapes as classes, behaviours dispatched on shape conformance.
//
//   const program = await load(shexc, options)
//   const alice   = program.object('http://example.org/alice', store)
//   await alice.call('greet', { greeting: 'Hello' })

import ShExParser from '@shexjs/parser';
import validatorPkg from '@shexjs/validator';
import neighborhoodPkg from '@shexjs/neighborhood-rdfjs';
import N3 from 'n3';

import { parseDef } from './decl.js';
import { NS, VALUE, fieldsOf, describeValueExpr, asTypeOf, localName, project, inject, functionalUpdate, termOf, idOf, jsonSafe } from './fields.js';
import { generateSource, compile, toWasmRecord, scalarTypeOf } from './ascompile.js';
import { ADAPTERS, EFFECT_OF } from './adapters.js';

const { ShExValidator } = validatorPkg;
const { ctor: RdfJsDb } = neighborhoodPkg;
const { namedNode, blankNode, quad } = N3.DataFactory;

const COMBINATORS = ['pipe', 'map']; // bindings defined in terms of other behaviours

export class DispatchError extends Error {}
export class AmbiguousDispatchError extends DispatchError {}
export class BehaviourTypeError extends TypeError {}

// A node seen in a particular graph. Graphs are treated as immutable values: behaviours that
// "change" an object return a new Obj over a new graph, and the original is left as it was.
export class Obj {
  constructor(program, node, graph, declaredShape, byValue = false) {
    this.program = program; this.node = idOf(termOf(node)); this.graph = graph;
    this.declaredShape = declaredShape; // the static type this object was returned or requested at, if any
    this.byValue = byValue; // true when it came back from a behaviour as a record (functional update)
  }
  call(name, args, opts) { return this.program.call(name, this.node, this.graph, args, opts); }
  conforms(shape) { return this.program.conforms(this.node, this.graph, shape); }
  shapes() { return this.program.shapesOf(this.node, this.graph); }
  record(shape) { return this.program.record(this.node, this.graph, shape ?? this.declaredShape); }
}

export async function loadFile(path, options = {}) {
  const fs = await import('node:fs/promises');
  const { pathToFileURL } = await import('node:url');
  const { dirname, resolve } = await import('node:path');
  const abs = resolve(path);
  return load(await fs.readFile(abs, 'utf8'), { base: pathToFileURL(abs).href, baseDir: dirname(abs), ...options });
}

export async function load(shexc, options = {}) {
  const program = new Program(shexc, options);
  await program._compile();
  return program;
}

export class Program {
  constructor(shexc, options) {
    this.options = options;
    this.base = options.base || 'http://a.example/';
    this.schema = ShExParser.construct(this.base, {}, { index: true }).parse(shexc);
    this.prefixes = this.schema._prefixes || {};
    delete this.schema._index; // rebuilt by the validator once generated shapes are merged in
    this.methods = [];
    this.generics = new Map(); // name -> [method]
    this.wheres = new Map(); // key -> where
    this.userShapes = this.schema.shapes.map((d) => d.id);
    this._validators = new WeakMap();
    this._memo = new Map();
    this._ctx = {
      options,
      asExports: null,
      wasmInstances: new Map(),
      mcpClients: new Map(),
      fetch: options.fetch || ((...a) => globalThis.fetch(...a)),
      resolveModule: options.resolveModule || ((iri) => this._resolveModule(iri)),
    };
    this._collect();
  }

  // ---- loading ----------------------------------------------------------------------------------

  _fragment(label, body, what) {
    try {
      return ShExParser.construct(this.base, { ...this.prefixes }, {}).parse(`<${label}> ${body}`).shapes[0];
    } catch (e) {
      throw new SyntaxError(`${what}: not valid ShExC: ${body}\n${e.message}`);
    }
  }

  _collect() {
    const generated = [];
    let prelude = '';
    for (const act of this.schema.startActs || []) if (act.name === NS + 'as') prelude += (act.code || '') + '\n';
    this.prelude = prelude;

    for (const decl of this.schema.shapes) {
      for (const shape of ownShapes(decl.shapeExpr)) {
        for (const act of shape.semActs || []) {
          if (act.name === NS + 'def') this._addMethod(decl.id, parseDef(act.code || ''), generated);
          else if (act.name === NS + 'where') this._addWhere(act, { level: 'shape', shapeId: decl.id });
        }
        forEachTripleConstraint(shape.expression, (tc) => {
          for (const act of tc.semActs || []) {
            if (act.name !== NS + 'where') continue;
            const d = describeValueExpr(tc.valueExpr);
            this._addWhere(act, { level: 'tc', shapeId: decl.id, predicate: tc.predicate, oType: d.kind === 'literal' ? asTypeOf(d.datatype) : 'string' });
          }
        });
      }
    }

    this.schema.shapes.push(...generated);
    this.shapeIndex = Object.fromEntries(this.schema.shapes.map((d) => [d.id, d]));
    this._ancestors = new Map();

    for (const m of this.methods) {
      m.selfFields = fieldsOf(m.shapeId, this.shapeIndex);
      m.paramFields = m.paramsShape ? fieldsOf(m.paramsShape, this.shapeIndex) : [];
      if (m.paramFields.some((f) => f.name === 'self')) throw new SyntaxError(`${m.label}: a parameter cannot be called 'self'`);
      const rf = fieldsOf(m.returnShape, this.shapeIndex)[0];
      if (!rf) throw new SyntaxError(`${m.label}: cannot read the return type '${m.decl.returns}'`);
      m.returnField = rf;
      if (rf.kind === 'ref') m.returnRefFields = fieldsOf(rf.refShape, this.shapeIndex);
    }
    for (const w of this.wheres.values()) if (w.level === 'shape') w.selfFields = fieldsOf(w.shapeId, this.shapeIndex);

    this._checkGenerics();
    this._inferEffects();
  }

  _addMethod(shapeId, decl, generated) {
    const id = this.methods.length;
    const label = `${this.shorten(shapeId)}.${decl.name}`;
    if (this.methods.some((m) => m.shapeId === shapeId && m.name === decl.name)) throw new SyntaxError(`${label} is defined twice`);
    const m = { id, name: decl.name, doc: decl.doc, label, shapeId, decl, binding: decl.binding, declaredEffect: decl.effect, paramsShape: null };
    if (decl.params) {
      m.paramsShape = `urn:shexb:params:${id}`;
      generated.push(this._fragment(m.paramsShape, `{ ${decl.params} }`, `${label} parameters`));
    }
    m.returnShape = `urn:shexb:ret:${id}`;
    const ret = this._fragment(m.returnShape, `{ <${VALUE}> ${decl.returns} }`, `${label} return type`);
    generated.push(ret);
    // A second declaration holding just the value expression, so that each returned value can be
    // validated as a focus node without writing temporary triples into anybody's graph.
    const tc = ret.shapeExpr.expression;
    m.returnValueShape = tc.valueExpr === undefined ? null : `urn:shexb:retv:${id}`;
    if (m.returnValueShape) generated.push({ type: 'ShapeDecl', id: m.returnValueShape, shapeExpr: tc.valueExpr });
    if (decl.binding.kind === 'as') m.asExport = `m${id}_${decl.name}`;
    this.methods.push(m);
    if (!this.generics.has(m.name)) this.generics.set(m.name, []);
    this.generics.get(m.name).push(m);
  }

  _addWhere(act, info) {
    const key = `w${this.wheres.size}`;
    this.wheres.set(key, { key, code: (act.code || '').trim(), ...info });
    act.code = key; // the handler is given only the code text, so the text becomes the lookup key
  }

  _checkGenerics() {
    const sig = (m) => JSON.stringify(m.paramFields.map((f) => [f.name, f.predicate, f.kind, f.datatype, f.refShape, f.min, f.max]));
    for (const [name, methods] of this.generics) {
      const first = sig(methods[0]);
      const odd = methods.find((m) => sig(m) !== first);
      if (odd) throw new SyntaxError(`all definitions of '${name}' must declare the same parameters (${methods[0].label} and ${odd.label} differ)`);
    }
  }

  _inferEffects() {
    const visiting = new Set();
    const effectOfGeneric = (name) => {
      const methods = this.generics.get(name);
      if (!methods) throw new SyntaxError(`reference to an unknown behaviour '${name}'`);
      return methods.some((m) => effectOf(m) === 'io') ? 'io' : 'pure';
    };
    const effectOf = (m) => {
      if (m.effect) return m.effect;
      if (!COMBINATORS.includes(m.binding.kind)) return (m.effect = EFFECT_OF[m.binding.kind]);
      if (visiting.has(m)) throw new SyntaxError(`${m.label}: ${m.binding.kind} definitions are circular`);
      visiting.add(m);
      const steps = m.binding.kind === 'pipe' ? m.binding.steps : [m.binding.behaviour];
      const e = steps.some((s) => effectOfGeneric(s) === 'io') ? 'io' : 'pure';
      visiting.delete(m);
      return (m.effect = e);
    };
    for (const m of this.methods) {
      const inferred = effectOf(m);
      if (m.declaredEffect === 'pure' && inferred === 'io') throw new SyntaxError(`${m.label} is declared pure but its ${m.binding.kind} binding performs io`);
      if (m.declaredEffect === 'io') m.effect = 'io';
      if (m.binding.kind === 'pipe') this._checkPipe(m);
      if (m.binding.kind === 'map') this._checkMap(m);
    }
  }

  _checkMap(m) {
    const field = m.selfFields.find((f) => f.name === m.binding.field);
    if (!field || !(field.kind === 'ref' || field.kind === 'iri')) throw new SyntaxError(`${m.label}: map needs a node-valued field of ${this.shorten(m.shapeId)}, and '${m.binding.field}' is not one`);
    if (this.generics.get(m.binding.behaviour).some((s) => s.paramFields.some((f) => f.min > 0))) throw new SyntaxError(`${m.label}: '${m.binding.behaviour}' needs arguments, which map does not supply`);
  }

  _checkPipe(m) {
    m.binding.steps.forEach((step, i) => {
      const methods = this.generics.get(step);
      if (i > 0 && methods.some((s) => s.paramFields.some((f) => f.min > 0))) throw new SyntaxError(`${m.label}: '${step}' needs arguments, and only the first step of a pipe receives any`);
      if (i < m.binding.steps.length - 1) {
        const bad = methods.find((s) => !(s.returnField.single && (s.returnField.kind === 'ref' || s.returnField.kind === 'iri')));
        if (bad) throw new SyntaxError(`${m.label}: '${step}' must return exactly one node so that the next step has a receiver (${bad.label} returns ${bad.decl.returns})`);
      }
    });
  }

  async _compile() {
    const asMethods = this.methods.filter((m) => m.binding.kind === 'as');
    if (!asMethods.length && !this.wheres.size) return;

    const classNames = new Map();
    const classes = [];
    const classFor = (shapeId) => {
      if (!classNames.has(shapeId)) {
        let name = (localName(shapeId) || 'Shape').replace(/^[a-z]/, (c) => c.toUpperCase());
        while ([...classNames.values()].includes(name)) name += '_';
        classNames.set(shapeId, name);
        const fields = fieldsOf(shapeId, this.shapeIndex);
        classes.push({ className: name, fields, comment: `record for ${this.shorten(shapeId)}` });
        for (const f of fields) if (f.embedFields) classFor(f.refShape);
      }
      return classNames.get(shapeId);
    };
    const many = (f, t) => (f.single ? t : `Array<${t}>`);

    const functions = [];
    for (const m of asMethods) {
      const rf = m.returnField;
      const returnType = rf.kind === 'ref' && rf.byValue ? many(rf, classFor(rf.refShape)) : many(rf, rf.asType);
      functions.push({
        exportName: m.asExport,
        comment: `${m.label} -> ${m.decl.returns}`,
        params: [{ name: 'self', type: classFor(m.shapeId) }, ...m.paramFields.map((f) => ({ name: f.name, type: many(f, scalarTypeOf(f, classFor)) }))],
        returnType,
        code: m.binding.code,
      });
    }
    for (const w of this.wheres.values()) {
      functions.push({
        exportName: w.key,
        comment: `where on ${this.shorten(w.shapeId)}${w.predicate ? ' ' + this.shorten(w.predicate) : ''}: ${w.code.replace(/\s+/g, ' ')}`,
        params: w.level === 'tc' ? [{ name: 's', type: 'string' }, { name: 'p', type: 'string' }, { name: 'o', type: w.oType }] : [{ name: 'self', type: classFor(w.shapeId) }],
        returnType: 'bool',
        code: w.code,
      });
    }
    this.asSource = generateSource({ prelude: this.prelude, classes, functions, classFor });
    const compiled = await compile(this.asSource, { cacheDir: this.options.cacheDir });
    this._ctx.asExports = compiled.exports;
  }

  async _resolveModule(iri) {
    if (/^https?:/.test(iri)) return new Uint8Array(await (await this._ctx.fetch(iri)).arrayBuffer());
    const fs = await import('node:fs/promises');
    const { resolve } = await import('node:path');
    return fs.readFile(resolve(this.options.baseDir || '.', iri));
  }

  // ---- shapes and conformance ---------------------------------------------------------------------

  shorten(iri) {
    for (const [p, ns] of Object.entries(this.prefixes)) if (iri.startsWith(ns) && iri.length > ns.length) return `${p}:${iri.slice(ns.length)}`;
    const rel = iri.startsWith(this.base.replace(/[^/]*$/, '')) ? iri.slice(this.base.replace(/[^/]*$/, '').length) : null;
    return rel ? `<${rel}>` : `<${iri}>`;
  }

  resolveShape(shape) {
    if (this.shapeIndex[shape]) return shape;
    const bare = String(shape).replace(/^<|>$/g, '');
    const abs = new URL(bare, this.base).href;
    if (this.shapeIndex[abs]) return abs;
    throw new ReferenceError(`no shape ${shape} in this schema`);
  }

  ancestors(shapeId) {
    if (!this._ancestors.has(shapeId)) {
      const out = new Set();
      this._ancestors.set(shapeId, out);
      for (const shape of ownShapes(this.shapeIndex[shapeId]?.shapeExpr)) {
        for (const parent of shape.extends || []) {
          if (typeof parent !== 'string') continue;
          out.add(parent);
          for (const a of this.ancestors(parent)) out.add(a);
        }
      }
    }
    return this._ancestors.get(shapeId);
  }

  _validatorFor(store) {
    let entry = this._validators.get(store);
    if (!entry) {
      const validator = new ShExValidator(this.schema, RdfJsDb(store), {});
      if (this.wheres.size) validator.semActHandler.register(NS + 'where', { dispatch: (code, ctx) => this._runWhere(code, ctx, store) });
      entry = { validator, cache: new Map() };
      this._validators.set(store, entry);
    }
    return entry;
  }

  _runWhere(code, ctx, store) {
    const w = this.wheres.get(code);
    const fn = this._ctx.asExports[w.key];
    let ok;
    if (w.level === 'tc') {
      const q = ctx.triples[0];
      const o = q.object.termType !== 'Literal' ? idOf(q.object)
        : w.oType === 'string' ? q.object.value
        : w.oType === 'bool' ? q.object.value === 'true' || q.object.value === '1'
        : w.oType === 'i64' ? BigInt(q.object.value) : Number(q.object.value);
      ok = fn(idOf(q.subject), q.predicate.value, o);
    } else {
      ok = fn(toWasmRecord(project(store, ctx.node, w.selfFields), w.selfFields));
    }
    return ok ? [] : [{ type: 'WhereFailure', message: `where { ${w.code} } is false`, shape: w.shapeId }];
  }

  // The full ShEx validation result for node@shape.
  validate(node, store, shape) {
    const { validator } = this._validatorFor(store);
    return validator.validateShapeMap([{ node: shapeMapNode(node), shape: this.resolveShape(shape) }])[0];
  }

  conforms(node, store, shape) {
    const shapeId = this.resolveShape(shape);
    const { cache } = this._validatorFor(store);
    const key = `${typeof node === 'object' ? JSON.stringify(node) : node}|${shapeId}`;
    if (!cache.has(key)) cache.set(key, this.validate(node, store, shapeId).status === 'conformant');
    return cache.get(key);
  }

  shapesOf(node, store) {
    return this.userShapes.filter((s) => this.conforms(node, store, s));
  }

  record(node, store, shape) {
    const shapeId = this.resolveShape(shape);
    if (!this.conforms(node, store, shapeId)) throw new BehaviourTypeError(`${node} does not conform to ${this.shorten(shapeId)}: ${this.explain(node, store, shapeId)}`);
    return project(store, node, fieldsOf(shapeId, this.shapeIndex));
  }

  explain(node, store, shape) {
    const r = this.validate(node, store, shape);
    if (r.status === 'conformant') return 'conformant';
    const found = [];
    (function walk(x) {
      if (!x || typeof x !== 'object' || found.length >= 3) return;
      if (x.type === 'WhereFailure') found.push(x.message);
      else if (x.type === 'MissingProperty') found.push(`missing ${x.property}`);
      else if (x.type === 'TypeMismatch' || x.type === 'NodeConstraintViolation') found.push(`${x.type}${x.errors ? ': ' + [].concat(x.errors).join('; ') : ''}`);
      else if (x.type === 'ClosedShapeViolation' || x.type === 'ExcessTripleViolation') found.push(x.type);
      for (const v of Object.values(x)) walk(v);
    })(r.appinfo);
    return found.length ? found.join('; ') : JSON.stringify(r.appinfo).slice(0, 300);
  }

  object(node, store, declaredShape) {
    return new Obj(this, node, store, declaredShape && this.resolveShape(declaredShape));
  }

  // ---- dispatch -----------------------------------------------------------------------------------

  // The method that a call would run. Applicable methods are those whose shape the node conforms
  // to; the chosen one must be below every other applicable one in the EXTENDS order.
  select(name, node, store, opts = {}) {
    const methods = this.generics.get(name);
    if (!methods) throw new DispatchError(`no behaviour named '${name}'`);
    let applicable;
    if (opts.as) {
      const view = this.resolveShape(opts.as);
      if (!this.conforms(node, store, view)) throw new BehaviourTypeError(`${node} does not conform to ${this.shorten(view)}: ${this.explain(node, store, view)}`);
      const lineage = new Set([view, ...this.ancestors(view)]);
      applicable = methods.filter((m) => lineage.has(m.shapeId));
    } else {
      applicable = methods.filter((m) => this.conforms(node, store, m.shapeId));
    }
    if (!applicable.length) {
      throw new DispatchError(`'${name}' is not understood by ${node} (defined on ${methods.map((m) => this.shorten(m.shapeId)).join(', ')}; node conforms to ${this.shapesOf(node, store).map((s) => this.shorten(s)).join(', ') || 'none'})`);
    }
    const winners = applicable.filter((m) => applicable.every((o) => o === m || this.ancestors(m.shapeId).has(o.shapeId)));
    if (winners.length !== 1) {
      throw new AmbiguousDispatchError(`'${name}' on ${node} is ambiguous between ${applicable.map((m) => m.label).join(' and ')}; pass { as: shape } or define '${name}' on a shape that extends them`);
    }
    return winners[0];
  }

  async call(name, node, store, args = {}, opts = {}) {
    const method = this.select(name, idOf(termOf(node)), store, opts);
    return this._invoke(method, idOf(termOf(node)), store, args || {});
  }

  async _invoke(m, node, store, args) {
    this._checkArgs(m, store, args);
    const self = project(store, node, m.selfFields);
    // Arguments marked // b:embed true are passed as node ids and delivered as records.
    const sent = { ...args };
    for (const f of m.paramFields) {
      if (!f.embedFields || sent[f.name] === undefined) continue;
      const expand = (id) => project(store, id, f.embedFields);
      sent[f.name] = Array.isArray(sent[f.name]) ? sent[f.name].map(expand) : expand(sent[f.name]);
    }
    const envelope = { function: m.name, shape: m.shapeId, self, args: sent };

    let raw;
    const memoKey = m.effect === 'pure' && this.options.memo !== false && !COMBINATORS.includes(m.binding.kind) ? `${m.id}|${JSON.stringify(jsonSafe([self, sent]))}` : null;
    if (memoKey && this._memo.has(memoKey)) {
      raw = structuredClone(this._memo.get(memoKey));
    } else if (m.binding.kind === 'pipe') {
      raw = await this._pipe(m, node, store, args);
    } else if (m.binding.kind === 'map') {
      // Send the behaviour to every node in the field. Each send is dispatched separately.
      const targets = [].concat(self[m.binding.field] ?? []).map((v) => (typeof v === 'object' ? v.id : v));
      raw = await Promise.all(targets.map((id) => this.call(m.binding.behaviour, id, store)));
    } else {
      raw = await ADAPTERS[m.binding.kind](m, envelope, this._ctx);
      if (memoKey) this._memo.set(memoKey, structuredClone(raw));
    }
    return this._checkResult(m, raw, node, store);
  }

  async _pipe(m, node, store, args) {
    let current = new Obj(this, node, store);
    let result;
    for (const [i, step] of m.binding.steps.entries()) {
      result = await current.call(step, i === 0 ? args : {});
      if (i < m.binding.steps.length - 1) current = result;
    }
    return result;
  }

  _checkArgs(m, store, args) {
    let injected;
    try { injected = inject({ ...args, id: '_:call' }, m.paramFields); } catch (e) { throw new BehaviourTypeError(`${m.label}: ${e.message}`); }
    if (!m.paramsShape) return;
    // Arguments are validated as one call record against the parameter shape. The data graph is
    // only needed when an argument is a node whose shape has to be checked.
    const needsGraph = m.paramFields.some((f) => f.kind === 'ref' || f.kind === 'any');
    const scratch = new N3.Store(needsGraph ? store.getQuads(null, null, null, null) : []);
    scratch.addQuads(injected.quads);
    const validator = needsGraph || this.wheres.size ? this._validatorFor(scratch).validator : new ShExValidator(this.schema, RdfJsDb(scratch), {});
    const r = validator.validateShapeMap([{ node: '_:call', shape: m.paramsShape }])[0];
    if (r.status !== 'conformant') {
      throw new BehaviourTypeError(`${m.label}: arguments ${JSON.stringify(jsonSafe(args))} do not match { ${m.decl.params} }`);
    }
  }

  _checkResult(m, raw, node, store) {
    const rf = m.returnField;
    let graph = store;
    let values = raw === null || raw === undefined ? [] : Array.isArray(raw) ? raw : [raw];
    if (values.length && values.every((v) => v instanceof Obj)) { graph = values[values.length - 1].graph; values = values.map((v) => v.node); }
    if (values.length < rf.min || (rf.max !== -1 && values.length > rf.max)) {
      throw new BehaviourTypeError(`${m.label} returned ${values.length} value(s); ${m.decl.returns} allows ${rf.min}..${rf.max === -1 ? '*' : rf.max}`);
    }

    const nodeValued = rf.kind === 'ref' || rf.kind === 'iri';
    const focus = [];
    for (const v of values) {
      if (nodeValued && v && typeof v === 'object') {
        // by value: a record. Apply it as a functional update and carry on with the new graph.
        if (rf.kind !== 'ref') throw new BehaviourTypeError(`${m.label} returned a record where ${m.decl.returns} expects a node id`);
        let put;
        try { put = inject(v, m.returnRefFields, node); } catch (e) { throw new BehaviourTypeError(`${m.label}: ${e.message}`); }
        graph = functionalUpdate(graph, put.subject, m.returnRefFields, put.quads);
        focus.push(idOf(put.subject));
      } else if (nodeValued) {
        focus.push(String(v));
      } else {
        focus.push(v);
      }
    }

    if (m.returnValueShape) {
      const literalFocus = (v) => ({ value: String(v), type: rf.datatype || 'http://www.w3.org/2001/XMLSchema#string' });
      for (const v of focus) {
        const ok = nodeValued ? this.conforms(v, graph, m.returnValueShape) : this.conforms(literalFocus(v), graph, m.returnValueShape);
        if (!ok) {
          const why = nodeValued ? this.explain(v, graph, m.returnValueShape) : 'wrong datatype or facet';
          throw new BehaviourTypeError(`${m.label} returned ${JSON.stringify(jsonSafe(v))}, which is not a valid ${m.decl.returns} (${why})`);
        }
      }
    }

    const wrapped = nodeValued ? focus.map((id) => (rf.kind === 'ref' ? new Obj(this, id, graph, rf.refShape, rf.byValue) : id)) : focus;
    return rf.max === 1 ? wrapped[0] : wrapped;
  }

  async close() {
    for (const pending of this._ctx.mcpClients.values()) {
      try { (await pending).client.close(); } catch { /* already closed */ }
    }
    this._ctx.mcpClients.clear();
  }
}

// ---- ShExJ helpers -------------------------------------------------------------------------------

// Shape objects written directly in a declaration (not reached through references or EXTENDS).
function ownShapes(shapeExpr) {
  if (!shapeExpr || typeof shapeExpr === 'string') return [];
  if (shapeExpr.type === 'Shape') return [shapeExpr];
  if (shapeExpr.type === 'ShapeAnd' || shapeExpr.type === 'ShapeOr') return shapeExpr.shapeExprs.flatMap(ownShapes);
  return [];
}

function forEachTripleConstraint(te, fn) {
  if (!te || typeof te === 'string') return;
  if (te.type === 'TripleConstraint') fn(te);
  else for (const e of te.expressions || []) forEachTripleConstraint(e, fn);
}

function shapeMapNode(node) {
  if (typeof node === 'object' && node !== null && !node.termType) return node; // {value, type} literal
  return idOf(termOf(node));
}

export { fieldsOf, project, inject } from './fields.js';
export { NS } from './fields.js';
