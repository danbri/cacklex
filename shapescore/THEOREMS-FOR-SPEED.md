# Theorems that license optimisations

19 September 2026. Each entry names the Lean theorem, the optimisation it
makes sound, and the source that motivates it. Factoidal facts are from
`danbri/factoidal` at 30154c0: a survey of `formal/lean4/L4Factoidal` (module
and theorem counts only) and the abstract of `docs/shardborough-storage-spec.md`
(Alpha Draft 0.3, 1 September 2026). I read no Factoidal proof and none of the
IBK design notes; fit with those formats is argument until checked.

What the survey showed: SPARQL has 64 files and 483 theorems, Storage 60 and
467, Unified 20 and 776, RDFS 215, OWL 486, RDF 266. SHACL has 45, ShEx 2, RML
0. The shapes and mapping layers are the ones with nothing to connect them to
the proved storage and query layers. The theorems below are chosen to be that
connection.

## 1. Frame: a verdict depends on a region and on the schema's predicates

`lfp_frame`, `gfp_frame` (`Frame.lean`). Let `Rel` be the steps a catalogue
uses and `R` a set of nodes closed under `Rel`-arcs. If two graphs agree on
the `Rel`-arcs leaving `R`, every node of `R` gets the same verdict in both,
under LFP and under GFP. Nothing is assumed about other predicates or about
nodes outside `R`. The GFP form is obtained from the LFP form by duality
(KR 2026, Proposition 1), so ShEx and SHACL readings share one proof.

Licenses:
- Selective I/O. The Shardborough abstract describes immutable,
  predicate-partitioned blocks with separate indexes for narrow range reads.
  A validator may read only the partitions of the predicates in `Rel`; the
  theorem says the verdict is the same as on the whole dataset.
- Cache and index validity. A stored verdict for a node stays correct across
  any change that does not touch the `Rel`-arcs of its region. An index of
  verdicts can therefore be keyed by (schema, region) and invalidated by
  predicate and subject range, not wholesale.
- Parallelism and sharding. Disjoint closed regions validate independently,
  and a shard that is closed under `Rel` validates locally.
- On-demand validation. The ShEx 2.0 specification says validation need not
  build a shape map over every node because the semantics implies a set of
  dependencies; Boneva et al. (arXiv 2503.24299, section 5) recall a recursive
  algorithm that computes only the relevant part of the maximal typing. The
  frame theorem is the statement that makes that algorithm correct.

Limit: proved for the executable fragment (single steps, either direction).
Atoms are taken as graph-independent; an atom such as `closed` reads the
graph, and then the agreement hypothesis must cover what it reads.

## 2. Append: which verdicts survive a delta

`lfp_append`, `gfp_shrink`, `rules_append` (`Frame.lean`).
- Catalogues without upper bounds or closedness (`Positive`, lower bounds
  over any path expression): every LFP verdict that held before an append
  holds after.
- Catalogues without lower bounds (`Universal`): a GFP violation is never
  repaired by adding triples.
- Forward-chained facts are monotone in the base graph.

Licenses: with an append-only delta log between generations (Shardborough
abstract), positive verdicts, recorded violations of universal constraints,
and inferred triples carry forward without recomputation, and the certificate
stages that justified them (`lfp_of_chain`) remain valid, because each stage
check is itself monotone. Only the mixed case, a shape with both a lower and
an upper bound through the same recursion, needs re-evaluation, and the frame
theorem bounds where. SHACL 1.2 Rules section 5.4 accumulates triples layer by
layer; `rules_append` is that monotonicity stated across generations. Negation
elements break it, which is why the draft's stratification condition (3.4.1)
matters for incremental maintenance as much as for meaning.

## 3. One solver, exact and total

`FinOp.solve_correct`, `FinOp.solve_isSome`, `FinOp.lfp_of_chain`
(`Generic.lean`). Any refinement of `step` that keeps `mem_step` (semi-naive
evaluation, an index-backed join, a block-at-a-time scan) inherits all three
with no further proof. That is the contract a fast engine has to meet, and it
is one lemma.

## 4. Counting is a triple expression

`sat_geq_iff_neigh` (`CountingAsTE.lean`). SHACL `sh:minCount` with a
qualified shape and the ShEx expression `{ (p @t){n} ; any* }` select the same
nodes. A single cardinality index per (predicate, target) serves both
languages, and a SHACL front end and a ShEx front end can compile to one
physical operator.

## 5. Certificates

`lfp_of_chain`, `gfp_of_postfixed`, `not_gfp_of_dual_chain`,
`not_lfp_of_dual_postfixed` (`Certificate.lean`). The verified side checks one
operator application per stage. The Shardborough abstract asks for explicit
evidence relating stored bytes to SPARQL results; for validation and inference
the evidence would be these stages, stored next to the derived blocks.

## Next theorems, by expected value

1. Semi-naive evaluation: for a `RuleKernel`, new conclusions of round k+1 use
   at least one fact first derived in round k. States as a `FinOp` whose
   `step` takes (total, delta) and satisfies the same `mem_step`.
2. Frame for rules: a rule layer whose body predicates lie in `Rel` is
   unaffected by other partitions. Same proof shape as `lfp_frame`.
3. Demand restriction: the answer to a goal equals the LFP of the operator
   restricted to the goal's dependency cone; this is backward chaining's
   correctness statement and it generalises section 1.
4. A bridge to Factoidal's SPARQL: `mem_step` for a CONSTRUCT evaluated by
   the existing algebra, so that its 483 theorems and these compose.
5. Stratified composition, and duality across strata.
