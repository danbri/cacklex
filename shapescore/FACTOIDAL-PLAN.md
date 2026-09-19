# ShapesCore and Factoidal: plan for contribution

Status: ShapesCore is a standalone Lake package on Factoidal's toolchain
(Lean 4.33.1), with no dependencies. It is not yet a candidate to replace
anything. This note says where it would go, what it would replace, and what
has to be true first. Facts about Factoidal are from `danbri/factoidal` at
commit `30154c0` (18 September 2026); I read the module headers and outlines,
not every line, and built none of it.

## What is there now

| | `L4Factoidal/SHACL/` | `L4Factoidal/ShEx/` |
| --- | --- | --- |
| Size | about 5,000 lines | about 3,600 lines |
| AST | `Path`, `Target`, `Constraint`, `Shape`, own `NodeKind` | `ShapeExpr`, `TripleExpr`, `NodeConstraint`, own `NodeKind` |
| Recursion | structural on fuel; out of fuel yields no violations | `partial def`; re-entry on a (label, node) pair assumes true, i.e. GFP, with negation stratification unchecked |
| Spec vs engine | `Spec.Conforms` relation and `validate` function; 45 theorems | engine only; two theorems, both lexer bounds |
| Harness | `l4shacl`, `l4shacl-rules`, `l4shacl-nodeexpr` | `l4shex` (1,182 validation entries), `l4shexc` |
| CI suites | `shacl-core`, `shacl12-core`, `shacl12-node-expr`, `shacl12-rules`, `shacl-sparql`, `shacl12-sparql` | `shex`, `shex-negative-syntax` |
| npm | served by the F* engine; Lean rejects | served by the F* engine; Lean rejects |

The two treatments share nothing: separate node-kind types, separate node
tests, separate recursion strategies, and no statement relating them.

## Placement

`formal/lean4/L4Factoidal/ShapesCore/`, namespace `L4Factoidal.ShapesCore`.
The move is a directory copy plus a namespace and import prefix change. The
core stays parametric in the node and predicate types; one new file,
`ShapesCore/RDF.lean`, instantiates `N := RDF.Term`, `P := WfIri` and builds a
`ShapesCore.Graph` from `RDF.Graph`. Nothing in the core imports RDF.

## What is replaced, and what is kept

Replaced, in the end: the two satisfaction engines (`SHACL.Validation`'s
recursive group; `ShEx.Satisfies` and `ShEx.Shapes`), and the two shape ASTs
as the thing semantics is defined on.

Kept and reused:
- both parsers and decoders (`SHACL.Shapes` decoding from a shapes graph,
  `ShEx.FromJson`, `ShEx.Compact`). They become front ends that compile to a
  ShapesCore catalogue plus an atom table;
- node tests: `ShEx.Validation.satisfiesNodeConstraint`, `XsdLexical`, and
  the SHACL value checks. Merged into one module and used as the atom
  interpretation `Ib`. This is the first shared piece and can land before
  anything else;
- SHACL's `evalPath` and its `superClasses` closure with their existing
  theorems, as the executable side of compound paths and of `sh:class` atoms;
- `SHACL.Report`, severity, messages: a reporting layer over core verdicts;
- SHACL-SPARQL, rules, node expressions: outside the core, unchanged.

## Gates

A stage is done when its gate holds in CI, not before.

1. Shared node tests. One node-constraint module used by the existing SHACL
   and ShEx engines. Gate: no change in any suite's pass count.
2. SHACL Core on ShapesCore, non-recursive. Front end from `SHACL.Shapes`
   to a catalogue; compound paths executable with a proof against
   `Path.Rel`. Gate: `shacl-core` and `shacl12-core` pass counts at least
   equal to the current engine's, and a theorem relating the front end's
   output to the existing `Spec.Conforms` on the fragment both cover.
3. ShEx on ShapesCore, single-occurrence fragment. Verified bag matcher for
   triple expressions where each predicate occurs once; everything else
   returns "outside fragment" (the npm `null`), never a guess. Gate: on the
   `shex` suite, zero wrong verdicts, and the declined count reported as
   its own column.
4. Full triple expressions. Verified partition search. Gate: `shex` pass
   count at least equal to `l4shex` today.
5. Recursion. Multi-stratum composition as a theorem; stratification
   checked by the front end, non-stratified schemas declined. ShEx runs
   GFP, SHACL runs LFP by default with GFP and "agreement" (LFP = GFP on the
   pair, which by `sms_determined` fixes every SMS reading) selectable.
   Gate: the thirteen tests of the KR 2026 paper as theorems or `#eval`
   checks; the sixteen `shex` entries the Satisfies header says the old fuel
   bound got wrong still pass.
6. EXTENDS / ABSTRACT. The specification is Boneva et al., Shape
   Expressions with Inheritance (arXiv 2503.24299), Tables 1 to 3 and
   Definitions 4 to 8; see DESIGN-NOTES.md section 4 for how it lands in the
   core and for one open reading question. Until it is done the existing
   `satisfiesExtends` stays, behind the same front end.
7. Switch-over. Wasm ops `shapesCompile`, `shapesCheck`, `shapesConforms`
   on compiled-schema handles; `l4-core` serves SHACL and ShEx from Lean
   for the first time; the old engines move to a differential-test role,
   then go.

Replacement candidate means gates 1 to 5. Gate 6 can trail, since EXTENDS is
not final in ShEx either.

## What the merge buys

- One termination and recursion story, proved, in place of fuel on one side
  and `partial` on the other.
- Per-shape verified checkers: `checkLfp G Ib C names nodes s` with
  `checkLfp_correct` as the specification.
- Statements that relate the two languages (duality, SMS bounds, later the
  fragment equivalence of KR 2026 Theorem 1) become possible at all.
- One npm surface: `shapes.compile(text, {syntax})` then `check` /
  `conforms`, with one meaning of `null`.

## Risks

- Performance. The core evaluator is naive (lists, full re-evaluation per
  round). The existing engines are not fast either, but this has to be
  measured on the suites before stage 2 is called done.
- SHACL 1.2 is a moving draft; list-valued `sh:datatype` / `sh:class` and
  reification constraints are atoms or front-end work, but the draft's
  eventual position on recursion decides the default in stage 5.
- The duality theorem for full triple expressions relies on `nneigh`, which
  has no surface syntax. It is a proof device. It must not leak into the
  front ends as if ShEx could express it.
