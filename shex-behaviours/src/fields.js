// Shape -> record field model, and the two directions of the mapping:
//   project(store, node, fields)  graph neighbourhood -> record   ("get")
//   inject(record, fields)        record -> quads                 ("put")
//
// Projection is defined for forward triple constraints reachable through EachOf/OneOf groups
// and EXTENDS. Other constructs (inverse constraints, nested anonymous shapes, NOT) still
// take part in validation but do not produce fields.

import N3 from 'n3';

const { namedNode, blankNode, literal, quad } = N3.DataFactory;

export const NS = 'https://example.org/shex-behaviours#';
export const XSD = 'http://www.w3.org/2001/XMLSchema#';
export const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
export const VALUE = 'urn:shexb:value'; // predicate used by generated return-type shapes

const I32 = ['int', 'short', 'byte', 'unsignedShort', 'unsignedByte'];
const I64 = ['integer', 'long', 'unsignedInt', 'unsignedLong', 'nonNegativeInteger', 'positiveInteger', 'negativeInteger', 'nonPositiveInteger'];
const F64 = ['double', 'decimal', 'float'];

// AssemblyScript scalar type used for a datatype IRI. Everything else travels as its lexical form.
export function asTypeOf(datatype) {
  if (!datatype || !datatype.startsWith(XSD)) return 'string';
  const local = datatype.slice(XSD.length);
  if (I32.includes(local)) return 'i32';
  if (I64.includes(local)) return 'i64';
  if (F64.includes(local)) return 'f64';
  if (local === 'boolean') return 'bool';
  return 'string';
}

export function localName(iri) {
  if (iri === RDF_TYPE) return 'type';
  const m = /([A-Za-z_][A-Za-z0-9_]*)$/.exec(iri.replace(/[#/:]+$/, ''));
  return m ? m[1] : null;
}

// ---- field extraction -------------------------------------------------------------------------

export function describeValueExpr(ve) {
  if (ve === undefined) return { kind: 'any' };
  if (typeof ve === 'string') return { kind: 'ref', refShape: ve, byValue: true };
  switch (ve.type) {
    case 'NodeConstraint':
      if (ve.datatype) return { kind: 'literal', datatype: ve.datatype };
      if (ve.nodeKind === 'literal') return { kind: 'literal', datatype: XSD + 'string' };
      if (ve.nodeKind === 'iri' || ve.nodeKind === 'bnode' || ve.nodeKind === 'nonliteral') return { kind: 'iri' };
      if (ve.values) {
        const lit = ve.values.find((v) => typeof v === 'object' && 'value' in v);
        return lit ? { kind: 'literal', datatype: lit.type || XSD + 'string' } : { kind: 'iri' };
      }
      return { kind: 'any' };
    case 'ShapeAnd':
    case 'ShapeOr': {
      const parts = ve.shapeExprs.map(describeValueExpr);
      const ref = parts.find((p) => p.kind === 'ref');
      // A reference combined with anything else is returned by reference (node id), not by value.
      if (ref) return { kind: 'ref', refShape: ref.refShape, byValue: false };
      return parts.find((p) => p.kind !== 'any') || { kind: 'any' };
    }
    default:
      return { kind: 'any' };
  }
}

function annotationValue(tc, predicate) {
  const a = (tc.annotations || []).find((x) => x.predicate === predicate);
  return a ? (typeof a.object === 'object' ? a.object.value : a.object) : undefined;
}

function walkTripleExpr(te, outer, out, tcIndex) {
  if (!te) return;
  if (typeof te === 'string') return walkTripleExpr(tcIndex[te], outer, out, tcIndex); // tripleExprRef
  const min = te.min === undefined ? 1 : te.min;
  const max = te.max === undefined ? 1 : te.max;
  const here = {
    optional: outer.optional || min === 0,
    repeated: outer.repeated || max === -1 || max > 1,
  };
  if (te.type === 'TripleConstraint') {
    if (te.inverse) return;
    out.push({
      predicate: te.predicate,
      name: annotationValue(te, NS + 'name') || localName(te.predicate),
      min: here.optional ? 0 : min,
      max: here.repeated ? -1 : max,
      embed: annotationValue(te, NS + 'embed') === 'true',
      ...describeValueExpr(te.valueExpr),
    });
  } else if (te.type === 'EachOf') {
    for (const e of te.expressions) walkTripleExpr(e, here, out, tcIndex);
  } else if (te.type === 'OneOf') {
    for (const e of te.expressions) walkTripleExpr(e, { ...here, optional: true }, out, tcIndex);
  }
}

function shapesIn(shapeExpr, shapeIndex, seen) {
  // The Shape objects that contribute triple constraints to a shape expression.
  if (!shapeExpr) return [];
  if (typeof shapeExpr === 'string') {
    if (seen.has(shapeExpr)) return [];
    seen.add(shapeExpr);
    const decl = shapeIndex[shapeExpr];
    return decl ? shapesIn(decl.shapeExpr, shapeIndex, seen) : [];
  }
  if (shapeExpr.type === 'ShapeDecl') return shapesIn(shapeExpr.shapeExpr, shapeIndex, seen);
  if (shapeExpr.type === 'Shape') {
    const parents = (shapeExpr.extends || []).flatMap((p) => shapesIn(p, shapeIndex, seen));
    return [...parents, shapeExpr];
  }
  if (shapeExpr.type === 'ShapeAnd') return shapeExpr.shapeExprs.flatMap((e) => shapesIn(e, shapeIndex, seen));
  return [];
}

export function fieldsOf(shapeId, shapeIndex, tcIndex = {}, embedding = []) {
  if (embedding.includes(shapeId)) throw new Error(`// b:embed forms a cycle: ${[...embedding, shapeId].join(' -> ')}`);
  const out = [];
  for (const shape of shapesIn(shapeId, shapeIndex, new Set())) {
    walkTripleExpr(shape.expression, { optional: false, repeated: false }, out, tcIndex);
  }
  // The same predicate constrained twice (for example in a parent and in an extension) is one field.
  const merged = new Map();
  for (const f of out) {
    const prev = merged.get(f.predicate);
    if (!prev) { merged.set(f.predicate, { ...f }); continue; }
    prev.min += f.min;
    prev.max = prev.max === -1 || f.max === -1 ? -1 : prev.max + f.max;
  }
  const fields = [...merged.values()];
  const names = new Set(['id']);
  for (const f of fields) {
    if (!f.name) throw new Error(`cannot derive a field name from <${f.predicate}> in ${shapeId}; add // b:name "…"`);
    if (names.has(f.name)) throw new Error(`field name '${f.name}' is used twice in ${shapeId}; add // b:name "…" to one of the constraints`);
    names.add(f.name);
    f.single = f.min === 1 && f.max === 1;
    f.asType = f.kind === 'literal' ? asTypeOf(f.datatype) : 'string';
    // // b:embed true : project the referenced node as a nested record instead of its id.
    if (f.embed && f.kind === 'ref') f.embedFields = fieldsOf(f.refShape, shapeIndex, tcIndex, [...embedding, shapeId]);
  }
  return fields;
}

// ---- terms and values -------------------------------------------------------------------------

export function termOf(id) {
  if (typeof id === 'object' && id !== null && id.termType) return id;
  return String(id).startsWith('_:') ? blankNode(String(id).slice(2)) : namedNode(String(id));
}

export function idOf(term) {
  return term.termType === 'BlankNode' ? '_:' + term.value : term.value;
}

function valueOfTerm(term, field) {
  if (term.termType !== 'Literal') return idOf(term);
  switch (field.asType) {
    case 'i32':
    case 'f64': return Number(term.value);
    case 'i64': { const n = Number(term.value); return Number.isSafeInteger(n) ? n : BigInt(term.value); }
    case 'bool': return term.value === 'true' || term.value === '1';
    default: return term.value;
  }
}

function termOfValue(value, field) {
  if (field.kind === 'ref' || field.kind === 'iri') return termOf(typeof value === 'object' && value !== null ? value.id : value);
  if (field.kind === 'literal') return literal(String(value), namedNode(field.datatype));
  if (typeof value === 'string' && /^[A-Za-z][A-Za-z0-9+.-]*:\S*$/.test(value)) return namedNode(value);
  if (typeof value === 'string' && value.startsWith('_:')) return blankNode(value.slice(2));
  if (typeof value === 'number') return literal(String(value), namedNode(XSD + (Number.isInteger(value) ? 'integer' : 'double')));
  if (typeof value === 'boolean') return literal(String(value), namedNode(XSD + 'boolean'));
  return literal(String(value));
}

const byLexical = (a, b) => (String(a) < String(b) ? -1 : String(a) > String(b) ? 1 : 0);

// get: the record for `node` as seen through `fields`. Multi-valued fields are sorted so that
// records are deterministic (RDF itself gives no order).
export function project(store, node, fields) {
  const subject = termOf(node);
  const record = { id: idOf(subject) };
  for (const f of fields) {
    let values = store.getObjects(subject, namedNode(f.predicate), null).map((t) => valueOfTerm(t, f)).sort(byLexical);
    if (f.embedFields) values = values.map((id) => project(store, id, f.embedFields));
    record[f.name] = f.single ? values[0] : values;
  }
  return record;
}

// put: the quads that a record stands for.
export function inject(record, fields, fallbackId) {
  const known = new Set(['id', ...fields.map((f) => f.name)]);
  for (const k of Object.keys(record)) if (!known.has(k)) throw new TypeError(`unknown field '${k}' (expected one of: ${[...known].join(', ')})`);
  const subject = termOf(record.id ?? fallbackId);
  const quads = [];
  for (const f of fields) {
    const v = record[f.name];
    const values = v === undefined || v === null ? [] : Array.isArray(v) ? v : [v];
    for (const x of values) quads.push(quad(subject, namedNode(f.predicate), termOfValue(x, f)));
  }
  return { subject, quads };
}

// A copy of `store` in which the field predicates of `subject` are replaced by `quads`.
export function functionalUpdate(store, subject, fields, quads) {
  const predicates = new Set(fields.map((f) => f.predicate));
  const next = new N3.Store();
  for (const q of store.getQuads(null, null, null, null)) {
    if (q.subject.equals(subject) && predicates.has(q.predicate.value)) continue;
    next.addQuad(q);
  }
  next.addQuads(quads);
  return next;
}

// JSON-safe copy of a record (BigInt has no JSON form).
export function jsonSafe(value) {
  return JSON.parse(JSON.stringify(value, (_, v) => (typeof v === 'bigint' ? (Number.isSafeInteger(Number(v)) ? Number(v) : v.toString()) : v)));
}
