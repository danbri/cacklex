// shapes-core.mjs: draft. A functional JavaScript mirror of the COMMON CORE of
// ShapesCore (the Lean modules Syntax, Semantics, Fixpoint, Duality, Exec,
// Iterate, Schema): node tests, and/or, shape names, counting over one step,
// LFP / GFP / SMS, duality, selectors. Nothing SHACL-only or ShEx-only:
// no compound paths, no triple expressions, no EXTENDS, no reports.
//
// Pure functions over plain frozen data. No classes, no mutation of inputs.
// Nothing here is verified; the Lean theorems it mirrors are named in comments.

const tag = (t, o = {}) => Object.freeze({ t, ...o });

// ---- syntax: one stratum, negation normal form ---------------------------------
export const top = tag('top');
export const bot = tag('bot');
export const atom = (e, pos = true) => tag('atom', { e, pos });     // fixed node test, negatable
export const ref = (s) => tag('ref', { s });                         // same-stratum name, positive only
export const and = (...xs) => xs.reduce((a, b) => tag('and', { a, b }));
export const or = (...xs) => xs.reduce((a, b) => tag('or', { a, b }));
export const fwd = (p) => tag('fwd', { p });
export const inv = (p) => tag('inv', { p });
const step = (st) => (typeof st === 'string' ? fwd(st) : st);
export const geq = (n, st, phi) => tag('geq', { n, st: step(st), phi });  // at least n successors satisfy phi
export const amn = (n, st, phi) => tag('amn', { n, st: step(st), phi });  // at most n successors FAIL phi
export const ex = (st, phi) => geq(1, st, phi);                       // SSL ∃p.φ
export const all = (st, phi) => amn(0, st, phi);                      // SSL ∀p.φ

// Lean: Shape.dual
export const dual = (f) => {
  switch (f.t) {
    case 'top': return bot;
    case 'bot': return top;
    case 'atom': return atom(f.e, !f.pos);
    case 'ref': return f;
    case 'and': return or(dual(f.a), dual(f.b));
    case 'or': return and(dual(f.a), dual(f.b));
    case 'geq': return f.n === 0 ? bot : amn(f.n - 1, f.st, dual(f.phi));
    case 'amn': return geq(f.n + 1, f.st, dual(f.phi));
  }
};
export const dualCatalogue = (C) => Object.fromEntries(Object.entries(C).map(([s, f]) => [s, dual(f)]));

// ---- graphs and assignments ------------------------------------------------------
export const graph = (triples) => Object.freeze(triples.map((t) => Object.freeze([...t])));
export const nodesOf = (G) => [...new Set(G.flatMap(([s, , o]) => [s, o]))];
const succ = (G, v, st) => [...new Set(
  st.t === 'fwd' ? G.filter(([s, p]) => s === v && p === st.p).map(([, , o]) => o)
                 : G.filter(([, p, o]) => o === v && p === st.p).map(([s]) => s))];

const key = (s, v) => `${s}\u0000${v}`;
export const asg = (pairs = []) => new Set(pairs.map(([s, v]) => key(s, v)));
export const holds = (a, s, v) => a.has(key(s, v));
export const pairsOf = (a) => [...a].map((k) => k.split('\u0000')).sort();
const sameSet = (a, b) => a.size === b.size && [...a].every((k) => b.has(k));
const subset = (a, b) => [...a].every((k) => b.has(k));

// ---- satisfaction (Lean: sat / evalB, related by evalB_iff) -----------------------
// I: atom name -> (node -> boolean)
export const sat = (G, I, a) => function go(f, v) {
  switch (f.t) {
    case 'top': return true;
    case 'bot': return false;
    case 'atom': return I[f.e](v) === f.pos;
    case 'ref': return holds(a, f.s, v);
    case 'and': return go(f.a, v) && go(f.b, v);
    case 'or': return go(f.a, v) || go(f.b, v);
    case 'geq': return succ(G, v, f.st).filter((u) => go(f.phi, u)).length >= f.n;
    case 'amn': return succ(G, v, f.st).filter((u) => !go(f.phi, u)).length <= f.n;
  }
};

// ---- the operator and the three semantics -----------------------------------------
// Lean: T
export const T = (G, I, C, nodes) => (a) =>
  asg(Object.keys(C).flatMap((s) => nodes.filter((v) => sat(G, I, a)(C[s], v)).map((v) => [s, v])));

// Lean: Correct (the supported-model condition)
export const isCorrect = (G, I, C, nodes) => (a) => sameSet(T(G, I, C, nodes)(a), a);

// Lean: solveLfp / solveLfp_correct. Kleene iteration from the empty assignment.
export const lfp = (G, I, C, nodes = nodesOf(G)) => {
  const op = T(G, I, C, nodes);
  const iterate = (a) => { const b = op(a); return sameSet(a, b) ? a : iterate(b); };
  return iterate(asg());
};

// Lean: gfp_iff_not_lfp_dual. GFP is the complement of LFP of the dual catalogue.
export const gfp = (G, I, C, nodes = nodesOf(G)) => {
  const l = lfp(G, I, dualCatalogue(C), nodes);
  return asg(Object.keys(C).flatMap((s) => nodes.filter((v) => !holds(l, s, v)).map((v) => [s, v])));
};

// Every SMS assignment, by brute force. Exponential: for tests on tiny graphs only.
export const supportedModels = (G, I, C, nodes = nodesOf(G)) => {
  const universe = Object.keys(C).flatMap((s) => nodes.map((v) => [s, v]));
  const subsets = universe.reduce((acc, p) => acc.flatMap((xs) => [xs, [...xs, p]]), [[]]);
  return subsets.map(asg).filter(isCorrect(G, I, C, nodes));
};

// ---- schemas (Lean: ConformsOn, conformsWith) --------------------------------------
// sel: [[shapeName, selectorShape]]; selectors mention no names.
export const conforms = (G, I, sel, nodes, a) =>
  sel.every(([s, sigma]) => nodes.every((v) => !sat(G, I, asg())(sigma, v) || holds(a, s, v)));

export const between = (lo, mid, hi) => subset(lo, mid) && subset(mid, hi);
