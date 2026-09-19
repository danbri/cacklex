# Source papers and specifications: working summaries

Summaries are in my own words and are meant as a reading guide for the Lean
code, not a substitute for the papers. "Read" means I fetched and read the full
text on 19 September 2026. "Not fetched" means the entry rests on how the two
read papers describe the work, plus prior knowledge, and should be checked
before being relied on.

## 1. Ahmetaj et al., Common Foundations for SHACL, ShEx, and PG-Schema (WWW 2025). Read.

arXiv 2502.01295, doi 10.1145/3696410.3714694. Fourteen authors including
Boneva, Labra Gayo, Martens, Polleres, Savković, Šimkus, Tomaszuk. Grew out
of Dagstuhl seminar 24102.

- Data model. A "common graph" is a set of edges N×P×N plus a partial map from
  (node, key) to a value, so it is a sub-model of both RDF and property
  graphs. Node identity is opaque: shapes cannot compare a node with a
  constant, only a value. There is no class mechanism.
- Schema. A schema is a set of (selector, shape) pairs, generalising ShEx shape
  maps and SHACL targets. A graph is valid when every node or value matching
  a selector satisfies the paired shape.
- SHACL is presented as a logic: ⊤, test(c), test(type), closed(Q), eq(π,p),
  disj(π,p), ¬, ∧, ∨, ∃≥n π.φ, ∃≤n π.φ, over path expressions with id, inverse,
  concatenation, union and star.
- ShEx is presented as a shape logic (tests, ∧, ∨, ¬) around triple
  expressions: ε, p.φ, p⁻.φ, e;e, e|e, e*, closed off by "any arc not in R/Q"
  tails. `;` and `*` split the neighbourhood into disjoint parts. Appendix C
  gives translations to and from ShEx 2.1 surface syntax, including how EXTRA
  and cardinality intervals reduce to these forms.
- The two languages count differently: ShEx counts triples at a node, SHACL
  counts nodes at the far end of a path. The paper gives a property each can
  express and the other cannot (equal numbers of p- and q-edges for ShEx;
  exactly two nodes reachable by p∪q for SHACL), with proofs.
- The shared core, CoGSL, is small: conjunctions of counting over single
  steps, star-free paths in existentials, and whole-neighbourhood closure.
  Proposition 1: every common schema has equivalent SHACL and ShEx schemas.
- Scope: non-recursive schemas only.

Use in the Lean code: the path grammar, `closedI`/`eqI`/`disjI`, the triple
expression grammar and its bag semantics, selectors as a separate layer.

## 2. Ahmetaj et al., Common Foundations for Recursive Shape Languages (KR 2026). Read.

Proceedings of KR 2026, pages 2–13, doi 10.24963/kr.2026/1; full version
arXiv 2604.20946. Same group, twelve authors. This is the paper the Lean
framework is built on.

- SSL, the Simple Shape Language: ⊥, ⊤, test(c), shape names, ¬, ∨, ∧, ∃p.φ,
  ∀p.φ. A catalogue maps names to shapes. Semantics is relative to a shape
  assignment α (which names hold at which nodes); α is correct when it is a
  fixpoint of the catalogue's operator.
- Three semantics. SMS accepts every correct assignment (brave or cautious
  when deciding conformance). LFP and GFP pick the least and greatest, defined
  for negation-free catalogues by Knaster–Tarski and extended to stratified
  ones by fixing lower strata first. Negation is allowed only on tests and on
  lower-stratum names.
- Duality (Proposition 1): swap ⊤/⊥, test/¬test, ∧/∨, ∃/∀ and keep names;
  then α is the LFP of C exactly when its complement is the GFP of the dual.
  So SSL under LFP and under GFP are equally expressive, and both match the
  alternation-free modal μ-calculus with nominals.
- Engines. Thirteen small tests separate the semantics. ShEx engines (rudof,
  Jena ShEx, ShEx-S) behave as GFP. SHACL engines mostly behave as brave SMS;
  TopBraid fits none of the four.
- Full languages. SHACL and ShEx are defined as SSL with richer shapes (the
  grammars of paper 1 plus names). Theorem 1: restricted ShEx under GFP (no
  star over `;`) and restricted SHACL under LFP (counting over single steps
  only, no eq/disj) are equally expressive, by translation through duality.
- Complexity: validation under LFP/GFP is polynomial in the data for all
  three languages; SMS is NP-hard even for SSL. Combined complexity for ShEx
  is P^NP (LFP/GFP) and NP^NP (SMS).
- Recommendation: SHACL should adopt LFP, ShEx keeps GFP, and the duality
  keeps them inter-translatable.

Use in the Lean code: everything in `Semantics`, `Fixpoint`, `Duality`, `SSL`
and `Examples` (bsep1 is their first separation test).

## 3. Boneva, Labra Gayo, Prud'hommeaux, Semantics and Validation of Shapes Schemas for RDF (ISWC 2017). Excerpt only.

Open version: arXiv 1404.1270. Seen today only as a search excerpt: shape
expressions are Boolean combinations of value and neighbourhood descriptions,
and stratified negation is defined through dep+ and dep- edges.

The reference semantics for ShEx 2.x with recursion and negation: typings,
stratified negation, maximal typing. Papers 1 and 2 take their ShEx
abstraction from it, and paper 2 identifies its semantics with GFP.

## 3a. Boneva, Labra Gayo, Prud'hommeaux, Thornton, Waagmeester, Shape Expressions with Inheritance (arXiv 2503.24299, 2025). Read.

The formal account of EXTENDS and ABSTRACT, to be submitted for the next ShEx
version under IEEE standardisation (P3330).

- Syntax: extendable labels have definitions `extends X h [and u]`: a set of
  parents, a shape, and an optional restriction. Only that form can be
  extended; disjunctions cannot, by design.
- Semantics: three mutually recursive relations. Triple expressions over sets
  of triples are as in ShEx 2.1 (disjoint union for `;` and `*`). New: a set
  of triples satisfying a shape expression (Table 3). Line 17 gives shapes
  with `closed` and `extra`; line 18 gives `extends`: partition the
  neighbourhood into a part for the shape and one part per ancestor, the
  ancestors taken as a set; ancestors' restrictions are checked on unions of
  parts; ancestors' `closed` and `extra` are ignored.
- Correct typings, abstract labels satisfied only through non-abstract
  descendants (Definition 4); dependency graph with `dep-extends` in both
  directions and the two negative dependencies, one of them for `extra`
  (Definitions 5 and 6); stratification and the maximal typing (7 and 8);
  correctness of the maximal typing and independence from the stratification
  (Proposition 1, Lemma 2).
- Validation is NP-complete, unchanged from ShEx 2.1; the refinement
  algorithm carries over.
- Section 6 compares with conjunction in ShEx 2.1 and in SHACL, and states
  the limitation that all descendants must be known.

Use in the Lean code: none yet. It is the specification for gate 6 of
FACTOIDAL-PLAN.md.

## 4. Staworko et al., Complexity and Expressiveness of ShEx for RDF (ICDT 2015). Not fetched.

Regular bag expressions, the single-occurrence fragment, NP-completeness of
matching in general. Relevant to a verified matcher: the tractable case is the
one where every predicate occurs once.

## 5. Corman, Reutter, Savković, Semantics and Validation of Recursive SHACL (ISWC 2018). Not fetched.

Introduced supported-model semantics for recursive SHACL and showed validation
NP-hard under it. Paper 2's `Correct` assignments are this notion.

## 6. Andreşel et al., Stable Model Semantics for Recursive SHACL (WWW 2020); Bogaerts and Jakubowski, Fixpoint Semantics for Recursive SHACL (ICLP 2021); Okulmus and Šimkus, SHACL Validation under the Well-founded Semantics (KR 2024). Not fetched.

The alternatives to SMS that paper 2 says the discussion is converging past,
toward LFP. Well-founded semantics is the natural next target if
non-stratified negation has to be given a meaning rather than rejected.

## 7. Bogaerts, Jakubowski, Van den Bussche, SHACL: A Description Logic in Disguise (LPNMR 2022) and Expressiveness of SHACL Features (LMCS 2024). Not fetched.

Source of the logical presentation of SHACL used in paper 1, and of the
results on what eq, disj and closed add.

## 8. Specifications

- SHACL 1.2 Rules, W3C Working Draft, 20 February 2026. Read in full. Rule
  sets in SRL or RDF syntax; abstract syntax with triple patterns, condition
  expressions, negation elements and assignments; well-formedness conditions
  on variables (3.2); rule dependency and the stratification condition (3.3,
  3.4); evaluation of a rule over solution sequences (5.3) and of a rule set
  layer by layer to a fixpoint (5.4). Much is marked as sketch or editor's
  note. Open issues: 749 (term creation), 752 (rule tuples, at risk), 765
  (rules on shapes), 516 (relation to CONSTRUCT), 779 (abbreviations, at
  risk), 780 (imports). Used by `Rules.lean` and ARCHITECTURE.md.

- SHACL 1.2 Core, W3C Working Draft (versions seen: 20 July, 23 July and
  3 August 2026), with companion drafts for SPARQL extensions, node
  expressions, rules, UI and profiling. From the overview and the TAG review
  request: list-valued datatype and class constraints, constraints on RDF 1.2
  reification (`sh:reifierShape`, `sh:reificationRequired`), severity and
  messages on individual constraints, `sh:ShapeClass`, node expressions for
  derived properties and for computing targets. I did not read the Core draft
  end to end, and did not find its current text on recursion.
- SHACL 1.2 Core editor's draft, section "Handling of Recursive Shapes",
  read as a search excerpt on 19 September 2026: recursion remains undefined
  and left to processors; shape-expecting parameters include sh:memberShape,
  sh:reifierShape and sh:someValue. w3c/data-shapes issue 565 asks for a
  defined behaviour.
- ShEx 2.1 (shex.io/shex-semantics), section 5.7.4 Negation Requirement, read
  as a search excerpt: a reference is negated under an odd number of ShapeNot
  or when the triple constraint's predicate is in the shape's `extra`; the
  dependency graph must have no cycle through a negated reference. Section
  5.2 defines stratification from it.
- ShEx 2.next (shex.io/shex-next and shex.io/extends-new-param), excerpts:
  `satisfies` gains an optional extended-neighbourhood argument; the negation
  requirement is stated over a "hierarchy and dependency graph" with edges
  both ways along extends; an "extends single shape requirement" limits what
  can be extended (shexSpec/shex issue 117).
