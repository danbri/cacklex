# ShapesCore

Module name ShapesCore; project codename CackleX. Planned as a contribution to the Factoidal repo (see FACTOIDAL-PLAN.md).

A Lean 4 core for shape languages, built on Ahmetaj et al., "Common
Foundations for Recursive Shape Languages" (KR 2026), with the SHACL and ShEx
constructs of their WWW 2025 paper added to the same syntax. SHACL 1.2 and
current ShEx are the targets; neither language is the foundation.

Lean 4.33.1, no dependencies (no Mathlib). `lake build` compiles everything;
`lake env lean Audit.lean` prints the axioms each main theorem uses. There is
no `sorry`, `partial`, `axiom` or `native_decide`. 2277 lines, 107 theorems.
Paper summaries are in PAPERS.md. The route into Factoidal, with gates, is in FACTOIDAL-PLAN.md. DESIGN-NOTES.md argues where SHACL and ShEx actually differ and what follows for the core. ARCHITECTURE.md describes the generic solver and how rules, paths, mappings, views and indices would use it.

## Design

One stratum of a catalogue is the unit. Its syntax is in negation normal form
with three kinds of leaf:

- `ref s`: a shape name of this stratum, positive only;
- `atom pos e`: anything already fixed, possibly negated. Node tests, value
  types, `closed`, `eq`, `disj`, `sh:class`, and the names of lower strata
  are all atoms, interpreted by a parameter `I : E → N → Prop`;
- `neigh e` / `nneigh e`: a ShEx triple expression over the node's
  neighbourhood, and its dual.

Counting is `geq n π φ` (SHACL `∃≥n π.φ`, over full path expressions) and
`amn n π φ`, "at most n nodes reached by π fail φ", which is the monotone
reading of an upper bound and the exact dual of `geq (n+1)`. SSL's `∃p.φ` and
`∀p.φ` are `geq 1` and `amn 0`.

Because same-stratum names occur only positively, every catalogue has a
monotone operator, so stratification is a property of the syntax and not a
side condition to check. `sh:not` and `sh:maxCount` over shapes of lower
strata are covered by `Shape.dual` on closed shapes (`sat_dual_closed`,
`sat_leq`).

Assignments are predicates `S → N → Prop`, so the fixpoint theory needs no
finiteness and no lattice library.

## What is proved

| Module | Result |
| --- | --- |
| `Semantics` | `sat_mono`: satisfaction is monotone in the assignment, for the whole syntax including paths, counting and triple expressions. Constructive. |
| `Fixpoint` | `lfp_correct`, `gfp_correct` (Knaster–Tarski); `correct_between`: every SMS assignment lies between LFP and GFP; `sms_determined`: where LFP and GFP agree, every SMS assignment agrees. Constructive. |
| `Duality` | `sat_dual`, `lfp_iff_not_gfp_dual`: KR 2026 Proposition 1 for one stratum, for the extended syntax and not only SSL. Classical. |
| `SSL` | `sat_ex`, `sat_all`: the derived forms have the semantics of the paper's Table 1. |
| `Frontends` | `sat_closed`, `sat_dual_closed`, `sat_leq`: closed shapes are assignment-independent, their dual is negation, and `∃≤n` on them has SHACL's meaning. |
| `Exec` | `evalB_iff`: a Bool evaluator decides `sat` on the executable fragment (atoms, names, ∧, ∨, counting over a single step, in either direction). Includes a from-scratch pigeonhole lemma. Uses the classical axioms (through `simp`/`omega`; not examined further). |
| `Iterate` | `solveLfp_correct`: if Kleene iteration from ∅ stabilises within fuel, the result is exactly LFP on the listed nodes. `gfp_iff_not_lfp_dual`, `checkLfp_correct`, `checkGfp_correct`: GFP is decided by solving the dual catalogue and complementing. |
| `Schema` | Selector maps and graph conformance (KR 2026 section 2.4); `conformsLfp_correct`, `conformsGfp_correct`. |
| `CountingAsTE` | `sat_geq_iff_neigh`: SHACL `∃≥n` over one step and the ShEx triple expression `{ (st.t){n} ; any* }` hold of the same nodes, on any duplicate-free graph, under any assignment. |
| `Certificate` | `lfp_of_chain`, `gfp_of_postfixed`, `not_gfp_of_dual_chain`, `not_lfp_of_dual_postfixed`: one-round verified checking of answers produced by an untrusted engine; refutations are proofs in the dual catalogue. |
| `Termination` | `solveLfp_isSome`: the fuel always suffices, so with `solveLfp_correct` the solver is total and exact. |
| `Generic` | `FinOp`: a finite monotone operator over any fact type, with `solve_correct`, `solve_isSome` and `lfp_of_chain` proved once for all instances. |
| `Rules` | Forward chaining as a `FinOp`: one layer of SHACL 1.2 Rules section 5.4. Runs the draft's section 2.1 example; `x_descendedFrom_c` checks one conclusion from a certificate. |
| `Frame` | `lfp_frame`, `gfp_frame`: verdicts on a region closed under the schema's steps depend only on the arcs of those steps leaving the region. `lfp_append`, `gfp_shrink`, `rules_append`: what survives an append. See THEOREMS-FOR-SPEED.md. |
| `ExamplesExec` | The paper's reach1 test is run with `#eval` (LFP = {a, b}, GFP = all four nodes, as the paper states) and the results are lifted by kernel `decide` to theorems about the declarative `lfp` and `gfp`; `reach1_separates`: one graph and schema conform under GFP and not under LFP. |
| `Examples` | The paper's separation test bsep1 as theorems: GFP accepts, LFP rejects, and the dual catalogue's GFP verdict follows from Proposition 1 in one line. |

The extension of Proposition 1 beyond SSL is mine, not the paper's. The paper
proves it for SSL and states Theorem 1 for restricted fragments; here the
dual of a ShEx neighbourhood shape is a primitive (`nneigh`), so duality
holds for unrestricted triple expressions, but `nneigh` has no ShEx surface
syntax. That is consistent with the paper's restriction, not a way round it.

## What is not done

1. The executable fragment stops short of compound paths (`π·π`, `π∪π`,
   `π*`) and of triple expressions. Paths need a verified reachability
   closure. Triple expressions need a verified bag matcher; start with the
   single-occurrence fragment, where matching is counting per predicate and
   `Graph.succ` plus the pigeonhole lemma already do most of the work.
2. The iteration is naive: every round re-evaluates every pair. With
   certificates (`Certificate`) the verified side need only run one round, so
   this matters less than it did.
3. One stratum only. A lower stratum's solved assignment can be passed in as
   `Ib`, which is how negation on lower-stratum names is obtained, but that
   composition and Proposition 1 across strata are not stated as theorems.
4. Selectors range over listed nodes only (see `Schema`).
5. Triple constraints point at names or atoms, not nested shapes (the paper's
   "shallow" form). Nested shapes need auxiliary names, a front-end rewrite.
6. ShEx EXTENDS/ABSTRACT, SHACL 1.2 reification constraints, node
   expressions, and severity/reporting are absent. EXTENDS is the one that
   needs semantic work; the others are atoms or reporting.
7. No translation theorems between the SHACL and ShEx fragments (paper
   Theorem 1), and nothing about the distinct-predicate fragment where
   counting triples and counting nodes coincide.
8. No parser and no link to `L4Factoidal`. `N` and `P` are type parameters;
   instantiating them with Factoidal's `Term` and IRI types, and its node
   constraint checker as `Ib`, is the integration point. Per-shape checkers
   are then `checkLfp G Ib C names nodes s` partially applied, with
   `checkLfp_correct` as their specification.
