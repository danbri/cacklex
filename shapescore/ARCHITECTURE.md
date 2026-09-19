# ShapesCore as a shared layer for Factoidal

19 September 2026. Working rule: claims are tied to a source, to a Lean
theorem, or marked as argument. Sources read for this note: SHACL 1.2 Rules,
W3C Working Draft of 20 February 2026 (read in full) [Rules12]; the header of
Factoidal's `L4Factoidal/SHACL/Rules.lean` at commit 30154c0 [FRules]. Not
read this round: the RML specification, Factoidal's Shardborough storage
specification (`docs/shardborough-storage-spec.md`), SPARQL 1.2. Everything
said about those three below is argument, to be checked against them.

## 1. What the SHACL 1.2 forward chainer is

[Rules12] section 5.4: stratify the rule set; for each layer, repeat "evaluate
every rule against the evaluation graph and add the triples not yet present"
until nothing is added. The result is the inference graph, the triples not in
the base graph. Section 5.3 evaluates a rule body left to right over solution
sequences: triple patterns join, condition expressions filter, a negation
element keeps a solution when its sub-body has no match, an assignment binds a
new variable. Section 3.4.1: evaluation is defined only when no recursive
dependency is negative; section 3.3 defines dependency between rules
syntactically, from whether a head template can generate a triple matching a
body pattern. Open in the draft: creating RDF terms (Issue 749, which notes
that inference can then be unbounded), rule tuples (752, at risk), attaching
rules to shapes (765, which asks what it would mean given the different
execution semantics), the relation to CONSTRUCT (516), and the TRANSITIVE /
SYMMETRIC / INVERSE abbreviations (779, at risk).

[FRules] implements exactly this by translating each RULE to a CONSTRUCT and
iterating, and marks its stratification check as a conservative approximation
and its filter-safety check as covering only the first FILTER.

One layer of [Rules12] 5.4 is a least fixpoint of a monotone operator on a
finite set of facts. That is the same object as a stratum of a shape
catalogue. ShapesCore now says so in one definition.

## 2. The abstraction: `FinOp` (proved)

`Generic.lean`. A `FinOp F` is, for any fact type `F`: a finite universe, an
executable round `step`, a declarative reading `Spec`, monotonicity, and one
bridge lemma `mem_step`. From those five fields:

  solve_correct   the solver's answer is exactly the least fixpoint
  solve_isSome    the solver always answers
  lfp_of_chain    a staged certificate from any engine checks in one round each

`Rules.lean` instantiates it for forward chaining and runs the example of
[Rules12] section 2.1; the solver returns the draft's stated conclusions, and
`x_descendedFrom_c` proves one of them from a three-stage certificate by
kernel evaluation. A shape catalogue is the instance with facts (name, node)
(`Iterate`, `Termination`, `Certificate` predate `Generic` and are the same
proofs; folding them onto it is mechanical and not yet done).

What each layer of Factoidal would supply (argument):

| Layer | Fact type | `Spec` | Notes |
| --- | --- | --- | --- |
| Shapes (SHACL, ShEx) | (name, node) | `sat` of the catalogue | GFP through the dual catalogue |
| SHACL rules | triple | some rule body matches | one `FinOp` per layer of [Rules12] 3.4 |
| Property paths | (node, node) per path | one more step | what `evalPath` computes; derived predicates of DESIGN-NOTES section 3 |
| RDFS / subclass closure | triple | fixed rule kernel | what `superClasses` computes |
| RML | triple | a mapping matches a source row | no recursion: one round, so `solve` stabilises at once |
| SPARQL CONSTRUCT / views | triple | the pattern matches | non-recursive `FinOp`; a view over a view is a second stratum |
| Indices | index entry | entry is implied by the data | an index is a materialised `FinOp`; see section 4 |

Stratified negation is uniform across the rows: a lower stratum's solved set is
passed to the next as fixed input. For shapes that input is the atom
interpretation; for rules it is the data that `NOT` consults. [Rules12] 3.4.1,
ShEx 2.1 5.7.4 and the KR 2026 paper's stratified catalogues are the same
condition on three dependency graphs.

## 3. Shapes and rules together (argument)

[Rules12] Issue 765 is open because validation and inference run differently.
With both as strata of one solver the combinations have definite meanings:

- validate the inferred graph: rules are lower strata, shapes above;
- rules conditioned on shapes (`?x` must conform to S): shapes below, rules
  above; S's solved assignment is fixed input to the rule layer;
- mutual recursion between a shape and a rule is one stratum over the sum type
  (name, node) + triple, legal exactly when every dependency is positive.

The third is the case no current specification defines. It costs nothing here
because `FinOp` does not care what a fact is.

## 4. Certificates and storage (argument)

A `FinOp` answer has a certificate checkable one round at a time
(`lfp_of_chain`), and non-membership has the dual kind (`Certificate.lean`,
for shapes). For a block-structured store this suggests: each materialised
derived set (closure, path index, inferred graph, validation result) is stored
with the stage at which each fact entered. Then (a) a reader can re-check any
block against its inputs without re-running the engine; (b) after an append,
old stages remain valid because `Spec` is monotone, and only new stages are
added; (c) deletion is the hard direction and needs the usual
delete-and-rederive treatment, which nothing here addresses. Whether this fits
Shardborough's manifests and segment layout has to be checked against its
specification, which I have not read.

## 5. What is not covered

- Term creation in rule heads ([Rules12] Issue 749). `FinOp` has a fixed
  universe; conclusions outside it are dropped. Skolemised or depth-bounded
  term creation would fit; unrestricted creation cannot, since termination is
  then false.
- Rule bodies are given as `single` and `join` functions, not as patterns. A
  verified pattern matcher and the binarisation of longer bodies are not
  written. [Rules12] 5.3's left-to-right evaluation with assignments is richer
  than what the kernel models.
- The dependency analysis of [Rules12] 3.3 and a checked stratification.
  [FRules] marks its own as approximate; a verified one would serve shapes,
  rules and ShEx's negation requirement alike, and is the natural next
  module.
- Multisets. [Rules12] 5.1 defines solution sequences as multisets, and rule
  tuples (at risk) keep duplicates. `FinOp` is about sets. For inference the
  difference vanishes at the head, since a graph is a set; for SPARQL SELECT
  it does not, so SELECT with duplicates is outside this abstraction.
- Aggregates, ordering, and anything else non-monotone in SPARQL.
- Performance: `step` is naive; semi-naive evaluation is a refinement of
  `step` with the same `mem_step`, so the theorems would carry over unchanged.
