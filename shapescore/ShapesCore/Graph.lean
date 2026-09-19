/-
Graphs, steps, paths and neighbourhoods.

Follows Ahmetaj et al., "Common Foundations for Recursive Shape Languages"
(KR 2026), section 2.1 and Definition 5: an RDF graph is a finite set of
triples; a path expression denotes a binary relation on nodes.

`N` is the type of nodes (IRIs, blank nodes and literals together) and `P`
the type of predicates. Nothing here depends on what they are.
-/
namespace ShapesCore

/-- A finite graph: a list of (subject, predicate, object) triples. -/
structure Graph (N P : Type) where
  triples : List (N × P × N)

/-- One edge traversal, forwards or backwards (`p` and `p⁻`). -/
inductive Step (P : Type) where
  | fwd (p : P)
  | inv (p : P)
deriving DecidableEq, Repr

/-- `G.arc v st u`: from `v`, the step `st` reaches `u`. -/
def Graph.arc {N P : Type} (G : Graph N P) (v : N) : Step P → N → Prop
  | .fwd p, u => (v, p, u) ∈ G.triples
  | .inv p, u => (u, p, v) ∈ G.triples

/-- SHACL path expressions: `id | q | π⁻ (on steps) | π·π | π∪π | π*`. -/
inductive Path (P : Type) where
  | id
  | step (st : Step P)
  | seq (a b : Path P)
  | alt (a b : Path P)
  | star (a : Path P)

/-- The relation a path denotes on a graph. -/
inductive Path.Rel {N P : Type} (G : Graph N P) : Path P → N → N → Prop where
  | id (v : N) : Rel G .id v v
  | step {st : Step P} {v u : N} : G.arc v st u → Rel G (.step st) v u
  | seq {a b : Path P} {v w u : N} : Rel G a v w → Rel G b w u → Rel G (.seq a b) v u
  | altL {a b : Path P} {v u : N} : Rel G a v u → Rel G (.alt a b) v u
  | altR {a b : Path P} {v u : N} : Rel G b v u → Rel G (.alt a b) v u
  | starNil {a : Path P} (v : N) : Rel G (.star a) v v
  | starCons {a : Path P} {v w u : N} : Rel G a v w → Rel G (.star a) w u → Rel G (.star a) v u

theorem Path.rel_step_iff {N P : Type} (G : Graph N P) (st : Step P) (v u : N) :
    Path.Rel G (.step st) v u ↔ G.arc v st u := by
  constructor
  · intro h; cases h; assumption
  · exact Path.Rel.step

/-- The neighbourhood Neigh±(v): outgoing arcs, then incoming arcs read
    backwards. A loop `(v, p, v)` appears twice, once in each direction, as in
    the paper. -/
def Graph.nbhd {N P : Type} [DecidableEq N] (G : Graph N P) (v : N) : List (Step P × N) :=
  G.triples.filterMap (fun t => if t.1 = v then some (Step.fwd t.2.1, t.2.2) else none)
  ++ G.triples.filterMap (fun t => if t.2.2 = v then some (Step.inv t.2.1, t.1) else none)

end ShapesCore
