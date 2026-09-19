/-
Forward-chaining rules as a `FinOp`: one stratification layer of SHACL 1.2
Rules (Working Draft of 20 February 2026), section 5.4, "while not finished:
for each rule: add the new triples".

Scope, against that draft:
- A rule is given by what it concludes from one triple (`single`) or from two
  (`join`). Rules with longer bodies binarise through helper predicates.
  Condition expressions and assignments over existing terms are just part of
  these functions.
- No new RDF terms. The draft's Issue 749 notes that creating terms can make
  inference unbounded. Here conclusions outside the supplied universe `U` are
  dropped, which is what makes `solve_isSome` true.
- `NOT { … }` is for a lower layer: section 3.4.1 requires that no recursive
  dependency is negative, so by the time a layer runs, negated patterns are
  fixed data, and `single`/`join` may consult them freely.
-/
import ShapesCore.Generic

namespace ShapesCore

abbrev Tr (N P : Type) := N × P × N

structure RuleKernel (N P : Type) where
  single : Tr N P → List (Tr N P)
  join : Tr N P → Tr N P → List (Tr N P)

def rulesOp {N P : Type} [DecidableEq N] [DecidableEq P]
    (G : List (Tr N P)) (K : RuleKernel N P) (U : List (Tr N P)) : FinOp (Tr N P) where
  U := U
  step a := U.filter fun f =>
    (decide (f ∈ G) || a.any (fun t => decide (f ∈ K.single t)))
      || a.any (fun t1 => a.any (fun t2 => decide (f ∈ K.join t1 t2)))
  Spec α f := (f ∈ G ∨ ∃ t, α t ∧ f ∈ K.single t) ∨ ∃ t1, α t1 ∧ ∃ t2, α t2 ∧ f ∈ K.join t1 t2
  spec_mono := by
    intro α β h f hs
    rcases hs with (hg | ⟨t, ht, hf⟩) | ⟨t1, h1, t2, h2, hf⟩
    · exact Or.inl (Or.inl hg)
    · exact Or.inl (Or.inr ⟨t, h t ht, hf⟩)
    · exact Or.inr ⟨t1, h t1 h1, t2, h t2 h2, hf⟩
  mem_step := by
    intro a f
    simp [List.mem_filter, List.any_eq_true]

/-! ## The example of section 2.1 of the draft -/

namespace RulesExample

inductive Nd where | A | B | C | X
deriving DecidableEq, Repr
inductive Pr where | fatherOf | motherOf | childOf | descendedFrom
deriving DecidableEq, Repr

def G : List (Tr Nd Pr) := [(.A, .fatherOf, .X), (.B, .motherOf, .X), (.C, .motherOf, .A)]

/-- RULE { ?x :childOf ?y } WHERE { ?y :fatherOf ?x }     (and :motherOf)
    RULE { ?x :descendedFrom ?y } WHERE { ?x :childOf ?y }
    RULE { ?x :descendedFrom ?y } WHERE { ?x :childOf ?z . ?z :childOf ?y } -/
def K : RuleKernel Nd Pr where
  single
    | (y, .fatherOf, x) => [(x, .childOf, y)]
    | (y, .motherOf, x) => [(x, .childOf, y)]
    | (x, .childOf, y) => [(x, .descendedFrom, y)]
    | _ => []
  join
    | (x, .childOf, z), (z', .childOf, y) => if z = z' then [(x, .descendedFrom, y)] else []
    | _, _ => []

def nodes : List Nd := [.A, .B, .C, .X]
def U : List (Tr Nd Pr) :=
  G ++ nodes.flatMap fun s => [Pr.childOf, Pr.descendedFrom].flatMap fun p => nodes.map fun o => (s, p, o)

def op : FinOp (Tr Nd Pr) := rulesOp G K U

#eval op.solve.map fun a => a.filter fun t => decide (t ∉ G)   -- the inference graph

def stages : List (List (Tr Nd Pr)) :=
  [G, [(.X, .childOf, .A), (.A, .childOf, .C)], [(.X, .descendedFrom, .C)]]

/-- The draft's stated conclusion, "X is descendedFrom C", as a checked
    certificate: three stages, each one round from the last. -/
theorem x_descendedFrom_c : op.lfp (.X, .descendedFrom, .C) :=
  op.lfp_of_chain stages (by decide) [(.X, .descendedFrom, .C)] (by simp [stages]) _ (by simp)

end RulesExample
end ShapesCore
