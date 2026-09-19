# Design notes: where SHACL and ShEx actually differ

19 September 2026, revised the same day against the source texts. Working rule
for this project: every claim is tied to a specification or paper section, to
a Lean theorem, or is marked as argument. Sources and how much of each I read
are listed in PAPERS.md. Short keys used below:

  [ShEx21]   Shape Expressions Language 2.1, shex.io/shex-semantics
  [ShExNext] Shape Expressions Language 2.next, shex.io/shex-next
  [Inh25]    Boneva, Labra Gayo, Prud'hommeaux, Thornton, Waagmeester,
             Shape Expressions with Inheritance, arXiv 2503.24299
  [CF25]     Ahmetaj et al., Common Foundations for SHACL, ShEx, and
             PG-Schema, WWW 2025
  [CFR26]    Ahmetaj et al., Common Foundations for Recursive Shape
             Languages, KR 2026
  [SHACL12]  SHACL 1.2 Core, editor's draft, w3c.github.io/data-shapes

## 1. The dividing line is node identity, not syntax

Everything in the shared core is invariant under unravelling the graph: a
shape cannot tell a node reached twice from two separate copies of it. The KR
2026 paper says this of ShEx when it excludes `eq` and `disj` from the
equi-expressive fragments. The SHACL features that fall outside are exactly
the ones that compare far-end nodes for identity: `eq`, `disj`, and counting
the endpoints of a compound path or of a union of predicates.

So the useful question about a feature is not "is it SHACL or ShEx" but "does
it need to know that two paths end at the same node". That gives a test that
can be applied to SHACL 1.2 additions as they arrive.

## 2. Counting is a triple expression (proved)

`sat_geq_iff_neigh` in `CountingAsTE.lean`: on a graph without duplicate
triples, under any assignment,

    ∃≥n st.t    iff    { (st.t){n} ; any* }

No distinct-predicate condition is needed. Over a single step, distinct
triples and distinct far-end nodes coincide because an RDF graph is a set. The
proof is a partition argument over permutations of the arc list.

Not yet proved, same method: "at most n fail φ" is
`{ (st.t)* ; (st.⊤){0,n} ; others* }`. It needs a `⊤` target, a one-line
addition to `Target`.

Consequence: the core needs one neighbourhood constructor, not three. `geq`
and `amn` are triple expressions of a fixed form, and SHACL's property shapes
are ShEx shapes whose triple constraints are intervals on one predicate each.
The general form behind both is a labelling: assign every arc to a constraint
symbol it is compatible with, such that the bag of symbols is in a given
language. That is monotone in the assignment by construction, which is why
recursion through it is safe.

## 3. Compound paths are a graph-side pre-pass (argued, not proved)

Two observations.

(a) An existential over a path is recursion. `∃π*.φ` is the name
`Y := φ ∨ ∃π.Y` under LFP; concatenation nests, union is `∨`. This is the
standard translation of PDL into the μ-calculus. So non-recursive SHACL with
star paths already lives inside the recursive core, and `sh:class` is in the
common core after all:

    K      := test(C) ∨ ∃ rdfs:subClassOf . K
    classC := ∃ rdf:type . K

(b) For everything else about paths, materialise each compound path that
occurs in a schema as a derived predicate, and work on the saturated graph G⁺.
A path does not depend on the assignment, so this can be done before any
fixpoint is taken. On G⁺, `∃≥n π.φ` is single-step counting over `p_π`, and by
section 2 that is a triple expression. If the path algebra has intersection
and difference, `eq(π, p)` and `disj(π, p)` become "no successor along
`p_{π∖p}`" and so on, and `closed(Q)` is "no successor along any-except-Q".

This gives a two-phase architecture:

  phase 1  graph side, assignment-independent: relation algebra over
           predicates. Factoidal's `evalPath` and `superClasses`, with their
           existing theorems, are this phase. SHACL 1.2 derived properties and
           SHACL rules are the same kind of thing.
  phase 2  shape side: atoms, names, one neighbourhood constructor, fixpoints.
           Single steps only, over base and derived predicates.

In these terms SHACL is a rich phase 1 with interval-shaped phase 2
constraints; ShEx is a trivial phase 1 with regular-bag phase 2 constraints.
The common language is trivial phase 1 with intervals. The union, rich phase 1
with bags, is still monotone and still polynomial in the data, and it
expresses both of the WWW 2025 paper's separating examples. Derived predicates
are where unravelling invariance is given up, deliberately and in one place.

A standards-facing reading: ShEx could adopt a path layer without touching its
triple-expression semantics, and SHACL could adopt bag constraints without
touching its paths.

## 4. EXTRA is stratified negation; EXTENDS is a labelled partition (sourced, then argued)

EXTRA, from the sources. [ShEx21] section 5.7.4 (Negation Requirement) counts
a reference from s1 to s2 as negated when it sits under an odd number of
ShapeNot, or when the triple constraint's predicate is in s1's `extra`. [Inh25]
has the same thing as the dependency `dep-extra-neg` (before Definition 5) and
forbids it on cycles (Definition 6). Its Table 3, line 17, gives the meaning:
the triples that match some triple constraint of `e` must satisfy `e`; the
other triples on predicates of `e` are allowed only on `extra` predicates. The
base case of its Proposition 1 spells out the consequence: within one stratum
no reference occurs under an extra predicate. [CF25] Appendix C.4.4 writes the
negation out. So EXTRA is a front-end rewrite onto `Shape.dual` of a closed
shape (`sat_dual_closed`), and the stratification check the core's syntax
imposes is the one the specification already requires. This was recollection
in the first version of these notes; it is now checked.

EXTENDS, from [Inh25]. Table 3, line 18: for `extends X h`, the neighbourhood
M is split as M' plus one part M_x for every x in anc(X), the SET of
ancestors. M' satisfies h; each M_x satisfies ext-te(x), the triple expression
of that ancestor's shape; and each ancestor's restriction (`and u` in its
definition) is checked against the union of the parts of its own ancestors.
Three details matter for the core:

- anc(X) is a set, so under multiple inheritance a shared ancestor is used
  once. The paper's example is ColouredCircle, which gets one `coord` through
  two routes. EXTENDS is therefore not the `;` of the parents' expansions.
- The ancestors' `closed` and `extra` are ignored; only ext-te(x) is used
  (Related work, and Example 5 with x5 and x6).
- Restrictions are evaluated on sub-neighbourhoods. That needs the second
  satisfaction relation of Table 3, "a set of triples satisfies a shape
  expression".

Only expressions of the form `extends X h [and u]` can be extended; extending
a disjunction is excluded on purpose (Design choices). [ShExNext] states a
matching "extends single shape requirement", and shexSpec/shex issue 117 asks
for use cases before relaxing it.

In core terms (argument): plain sequential composition of bags is not enough,
because restrictions speak about unions of parts. The labelling form of
section 2 is: label each arc with a constraint symbol, where a symbol now
carries the ancestor it belongs to; the bag of labels with tag x must be in
the language of ext-te(x); and restr(x) is a constraint on the arcs whose tag
is in anc(x). `TE.Matches.mono` carries over, since a restriction that is
positive in the typing stays positive on a sub-bag.

References and abstract labels. [Inh25] Definition 4 says an abstract label is
satisfied only through a non-abstract descendant, and section 2 says a node
satisfying a descendant satisfies the ancestor (f1 is a ColouredCircle, a
ColouredFigure, a Circle and a Figure). In the text I extracted, Definition 4
gives the non-abstract case as satisfaction of def(z) alone, which does not by
itself yield the f1 and Circle claim made under Limitations. Either the
extraction lost part of the definition or the mechanism sits elsewhere. This
has to be read in the PDF before any front end is written. [ShExNext] adds
edges in both directions between a label and what it extends to the dependency
graph used for the negation requirement; [Inh25] does the same with
`dep-extends`, and its Example 7 shows a schema that is ill-formed only
because of that edge. The Limitations paragraph names the cost: all
descendants must be known to validate a label, which is the non-local effect
seen in the behaviours prototype when `<Organization>` was removed.

Where predicates do not overlap. [Inh25] section 6 (Inheritance-like features
in ShEx 2.1) makes the point with Figure and Circle: conjunction gives
inheritance "because" the two shapes use disjoint sets of properties, and its
Product and MyProduct example shows conjunction failing once a property is
shared. The same section expects inheritance in SHACL to need conjunction.
That is the sourced form of the claim that `;` and `∧` coincide on shapes that
constrain each predicate once. The rest is my observation: that fragment is
also where bag matching is counting, where dispatch in the behaviours language
is cheap, and where its record mapping is well defined, so the front ends
should detect it.

## 5. Strata should carry their own fixpoint polarity (proposed)

[SHACL12], "Handling of Recursive Shapes": validation with recursive shapes is
still not defined and is left to processors; the list of shape-expecting
parameters now includes sh:memberShape, sh:reifierShape and sh:someValue.
w3c/data-shapes issue 565 asks for the behaviour to be defined. [CFR26]
recommends LFP for SHACL and fixes one polarity per language. Section 3(a) shows why a
catalogue wants both: `∃π*` is a least fixpoint and `∀π*` is a greatest one,
whatever the language default, because path semantics is reachability. A
stratified catalogue whose strata are each tagged μ or ν is the
alternation-free μ-calculus, which is the expressiveness the paper measures
against. ShEx front ends emit all ν, SHACL front ends all μ, and path
elimination adds strata of the other kind. Proposition 1 across strata flips
every tag and complements every solved assignment. The single-stratum case is
proved; the induction over strata is not written.

## 6. Verify the certificate, not the search (proved for the executable fragment)

`Certificate.lean`. An untrusted engine produces the answer; the verified side
applies the operator once.

  in LFP       a chain of stages, each derivable in one round from the last
  in GFP       one post-fixed set
  not in GFP   a chain for the dual catalogue
  not in LFP   a post-fixed set for the dual catalogue

The last two come from Proposition 1: a refutation is a proof in the dual
catalogue. None of the four theorems needs closed node lists or complete name
lists.

This matches how [Inh25] section 5 states the problem: validation is deciding
whether a given typing is contained in the maximal typing, and its
Proposition 1 rests on the union of correct typings being correct, which is
why any correct typing is a certificate. Its refinement algorithm, start from
the complete typing and remove failing pairs, is the downward mirror of
`solveLfp`.

Three consequences. A ShEx result shape map is a certificate of the second
kind, so a verified one-round checker can audit any ShEx engine's output,
Factoidal's F* build and other implementations included. For full triple
expressions the certificate carries the arc labelling, which shex.js already
reports as its solution; checking a labelling is linear, finding one is the
NP-hard part, so the verified bag matcher stops being a prerequisite. And the
naive evaluator's speed matters much less, since it runs for one round.

For the behaviours language: one solve yields every (shape, node) pair, which
is the whole dispatch table for a graph version; graphs there are immutable,
so it can be cached, and after a functional update `sat_local` says which part
of an old certificate still checks.

## 7. Termination (proved)

`solveLfp_isSome` in `Termination.lean`. Iterates from the empty assignment
grow; an unstable round adds a listed pair; the count of listed pairs still
missing strictly drops. With `solveLfp_correct`, the solver is total and
exact on the executable fragment.

## 8. Open, in order of value

1. The labelling form of the neighbourhood constructor, with `geq`, `amn` and
   `neigh` as instances, and a verified labelling checker for certificates.
2. Path elimination as a theorem: `∃π.φ` against the generated names.
3. Tagged strata and Proposition 1 across them.
4. Same-bag conjunction in triple expressions, then EXTENDS as a rewrite, to
   be tested against the EXTENDS entries of the `shex` suite.
5. Phase 1 over Factoidal's `evalPath`, with derived predicates.

## 9. Caveats

Checked against sources today: the EXTRA rule ([ShEx21] 5.7.4, [Inh25]), the
EXTENDS semantics ([Inh25] Tables 1 to 3, Definitions 4 to 8), SHACL 1.2's
position on recursion ([SHACL12]). Still recalled and not re-read: the
Presburger view of bag languages and the translation of PDL into the
μ-calculus, both used in sections 2 and 3. The edge-type abstraction is from
[CFR26] Proposition 2. Sections 3 and 5, and the "in core terms" paragraph of
section 4, are arguments. One open reading question on [Inh25] Definition 4 is
recorded in section 4. I read specification sections through search excerpts
for [ShEx21], [ShExNext] and [SHACL12], not the full documents.
