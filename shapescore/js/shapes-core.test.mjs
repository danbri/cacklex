// Tests for the common core only. Expected values are those printed in
// Ahmetaj et al., KR 2026, section 3, where a test comes from that paper.
// Run: node --test
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  top, atom, ref, and, or, ex, all, geq, amn, inv, dual, dualCatalogue,
  graph, nodesOf, asg, pairsOf, lfp, gfp, supportedModels, isCorrect, conforms, between, sat,
} from './shapes-core.mjs';

const is = (c) => (v) => v === c;
const pairs = (a) => pairsOf(a).map(([s, v]) => `${s}:${v}`).join(' ');

test('bsep1: one self-loop separates LFP from GFP', () => {
  const G = graph([['a', 'p', 'a']]);
  const C = { s: ex('p', ref('s')) };
  assert.equal(pairs(lfp(G, {}, C)), '');
  assert.equal(pairs(gfp(G, {}, C)), 's:a');
});

test('bsep2: SMS admits four assignments; LFP and GFP are its least and greatest', () => {
  const G = graph([['a', 'p', 'a'], ['b', 'p', 'b']]);
  const C = { s: ex('p', ref('s')) };
  const models = supportedModels(G, {}, C).map(pairs).sort();
  assert.deepEqual(models, ['', 's:a', 's:a s:b', 's:b']);
  assert.equal(pairs(lfp(G, {}, C)), '');
  assert.equal(pairs(gfp(G, {}, C)), 's:a s:b');
});

test('bsep3: mutual recursion between two names', () => {
  const G = graph([['a', 'p', 'c'], ['b', 'p', 'c']]);
  const C = { s: and(ref('t'), ex('p', top)), t: and(ref('s'), ex('p', top)) };
  assert.equal(pairs(lfp(G, {}, C)), '');
  assert.equal(pairs(gfp(G, {}, C)), 's:a s:b t:a t:b');
});

// b -> a, and c <-> d
const R = graph([['b', 'p', 'a'], ['c', 'p', 'd'], ['d', 'p', 'c']]);
const I = { isA: is('a') };

test('reach1: "can reach a" is an LFP property', () => {
  const C = { r: or(atom('isA'), ex('p', ref('r'))) };
  assert.equal(pairs(lfp(R, I, C)), 'r:a r:b');
  assert.equal(pairs(gfp(R, I, C)), 'r:a r:b r:c r:d');
});

test('safe1: "cannot reach a" is a GFP property, and is the dual of reach1', () => {
  const C = { s: and(atom('isA', false), all('p', ref('s'))) };
  assert.equal(pairs(lfp(R, I, C)), '');
  assert.equal(pairs(gfp(R, I, C)), 's:c s:d');
  // the dual keeps the name, so compare against safe1 written with the name r
  assert.deepEqual(dualCatalogue({ r: or(atom('isA'), ex('p', ref('r'))) }),
    { r: and(atom('isA', false), all('p', ref('r'))) });
});

test('conformance: the same schema and graph pass under GFP and fail under LFP', () => {
  const C = { r: or(atom('isA'), ex('p', ref('r'))) };
  const sel = [['r', top]];
  const nodes = nodesOf(R);
  assert.equal(conforms(R, I, sel, nodes, gfp(R, I, C)), true);
  assert.equal(conforms(R, I, sel, nodes, lfp(R, I, C)), false);
});

test('selectors: "subjects of p" behaves like sh:targetSubjectsOf and a ShEx shape map query', () => {
  const C = { r: or(atom('isA'), ex('p', ref('r'))) };
  const onlyB = [['r', and(ex('p', top), ex('p', atom('isA')))]];   // nodes with a p-edge to a
  assert.equal(conforms(R, I, onlyB, nodesOf(R), lfp(R, I, C)), true);
});

test('duality (Lean: lfp_iff_not_gfp_dual) on every catalogue above, every node', () => {
  const cases = [
    [graph([['a', 'p', 'a']]), {}, { s: ex('p', ref('s')) }],
    [R, I, { r: or(atom('isA'), ex('p', ref('r'))) }],
    [R, I, { s: and(atom('isA', false), all('p', ref('s'))) }],
    [R, I, { k: geq(1, inv('p'), ref('k')), m: amn(0, 'p', or(ref('m'), atom('isA'))) }],
  ];
  for (const [G, J, C] of cases) {
    const nodes = nodesOf(G);
    const l = lfp(G, J, C, nodes);
    const g = gfp(G, J, dualCatalogue(C), nodes);
    for (const s of Object.keys(C)) for (const v of nodes) {
      assert.equal(l.has(`${s}\u0000${v}`), !g.has(`${s}\u0000${v}`), `${s} at ${v}`);
    }
  }
});

test('SMS bounds (Lean: correct_between): every supported model lies between LFP and GFP', () => {
  const C = { r: or(atom('isA'), ex('p', ref('r'))), q: all('p', ref('q')) };
  const lo = lfp(R, I, C), hi = gfp(R, I, C);
  const models = supportedModels(R, I, C);
  assert.ok(models.length > 1);
  for (const m of models) assert.ok(between(lo, m, hi));
  assert.ok(isCorrect(R, I, C, nodesOf(R))(lo) && isCorrect(R, I, C, nodesOf(R))(hi));
});

test('counting over one step: minCount / maxCount / ShEx cardinality on a single predicate', () => {
  const G = graph([['x', 'author', 'p1'], ['x', 'author', 'p2'], ['y', 'author', 'p1'], ['z', 'title', 't']]);
  const J = { person: (v) => v.startsWith('p') };
  const twoAuthors = and(geq(2, 'author', atom('person')), amn(0, 'author', atom('person')));
  const check = (v) => sat(G, J, asg())(twoAuthors, v);
  assert.deepEqual(['x', 'y', 'z'].map(check), [true, false, false]);
  // upper bound on a closed shape: "at most one author" is "at most 1 fail not-person"
  const atMostOne = amn(1, 'author', dual(atom('person')));
  assert.deepEqual(['x', 'y', 'z'].map((v) => sat(G, J, asg())(atMostOne, v)), [false, true, true]);
});

test('dual is an involution up to meaning, not syntax (Lean: sat_dual_dual)', () => {
  const f = geq(0, 'p', top);                    // trivially true
  assert.notDeepEqual(dual(dual(f)), f);         // bot -> top, not geq 0
  for (const v of nodesOf(R)) assert.equal(sat(R, I, asg())(dual(dual(f)), v), sat(R, I, asg())(f, v));
});
