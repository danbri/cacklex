/-
Separation test `bsep1` of KR 2026 section 3, as theorems:
  G = {(a, p, a)},  C = {s : ∃p.s},  selector s : test(a).
GFP assigns s to a; LFP does not. Any engine can be placed by this one case.
-/
import ShapesCore.Frontends

namespace ShapesCore.Examples
open ShapesCore

inductive Nd where
  | a
deriving DecidableEq

def G1 : Graph Nd Unit := ⟨[(.a, (), .a)]⟩
def I0 : Empty → Nd → Prop := fun e _ => nomatch e
def C1 : Catalogue Unit Unit Empty := fun _ => .ex (.fwd ()) (.ref ())

theorem bsep1_gfp : gfp G1 I0 C1 () .a := by
  refine ⟨fun _ _ => True, ?_, trivial⟩
  intro s v _
  show sat G1 I0 _ (C1 s) v
  refine (sat_ex G1 I0 _ _ _ v).2 ⟨.a, ?_, ?_⟩
  · cases v; simp [Graph.arc, G1]
  · simp [sat]

theorem bsep1_lfp : ¬ lfp G1 I0 C1 () .a := by
  intro h
  refine h (fun _ _ => False) ?_
  intro s v ht
  obtain ⟨u, _, hu⟩ := (sat_ex G1 I0 _ _ _ v).1 ht
  simp [sat] at hu

/-- The dual catalogue is `s : ∀p.s`. Proposition 1 turns the LFP refusal
    above into a GFP acceptance for the dual, with no further work. -/
theorem bsep1_dual_gfp : gfp G1 I0 C1.dual () .a :=
  (gfp_dual_iff_not_lfp G1 I0 C1 () .a).2 bsep1_lfp

end ShapesCore.Examples
