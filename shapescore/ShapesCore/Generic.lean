/-
The solver, abstracted from shapes.

A `FinOp F` is a monotone operator on sets of facts of any type `F`, with a
finite universe, an executable round (`step`) and a declarative reading
(`Spec`) tied together by `mem_step`. Everything proved for shape catalogues
in `Iterate`, `Termination` and `Certificate` holds for any `FinOp`:

  solve_correct   the answer is exactly the least fixpoint
  solve_isSome    the solver always answers
  lfp_of_chain    an untrusted engine's answer can be checked in one round

Instances in this package: forward-chaining rules (`Rules`). A shape
catalogue is one too (facts are (name, node) pairs). The intended further
instances are listed in ARCHITECTURE.md.
-/
import ShapesCore.Termination

namespace ShapesCore

structure FinOp (F : Type) [DecidableEq F] where
  U : List F
  step : List F → List F
  Spec : (F → Prop) → F → Prop
  spec_mono : ∀ {α β : F → Prop}, (∀ f, α f → β f) → ∀ f, Spec α f → Spec β f
  mem_step : ∀ (a : List F) (f : F), f ∈ step a ↔ f ∈ U ∧ Spec (fun x => x ∈ a) f

namespace FinOp
variable {F : Type} [DecidableEq F] (O : FinOp F)

def T (α : F → Prop) : F → Prop := fun f => f ∈ O.U ∧ O.Spec α f
def lfp : F → Prop := fun f => ∀ α : F → Prop, (∀ g, O.T α g → α g) → α f

theorem T_mono {α β : F → Prop} (h : ∀ f, α f → β f) : ∀ f, O.T α f → O.T β f :=
  fun f hT => ⟨hT.1, O.spec_mono h f hT.2⟩

theorem T_lfp_le : ∀ f, O.T O.lfp f → O.lfp f := by
  intro f hT α hα
  exact hα f (O.T_mono (fun g hg => hg α hα) f hT)

theorem step_le_lfp (a : List F) (ha : ∀ f ∈ a, O.lfp f) : ∀ f ∈ O.step a, O.lfp f := by
  intro f hf
  obtain ⟨hu, hs⟩ := (O.mem_step a f).1 hf
  exact O.T_lfp_le f ⟨hu, O.spec_mono (fun x hx => ha x hx) f hs⟩

def stable (a : List F) : Bool := (O.step a).all (fun x => decide (x ∈ a))

theorem lfp_le_of_stable (a : List F) (hst : O.stable a = true) : ∀ f, O.lfp f → f ∈ a := by
  intro f hl
  refine hl (fun x => x ∈ a) ?_
  intro g hT
  have hm : g ∈ O.step a := (O.mem_step a g).2 hT
  simpa using List.all_eq_true.1 hst g hm

def iterUntil : Nat → List F → Option (List F)
  | 0, _ => none
  | k+1, a => if O.stable a then some a else iterUntil k (O.step a)

/-- Naive bottom-up evaluation: SHACL 1.2 Rules section 5.4, one layer. -/
def solve : Option (List F) := O.iterUntil (O.U.length + 1) []

theorem iterUntil_correct : ∀ (k : Nat) (a0 a : List F), (∀ f ∈ a0, O.lfp f) →
    O.iterUntil k a0 = some a → ∀ f, f ∈ a ↔ O.lfp f := by
  intro k
  induction k with
  | zero => intro a0 a _ h; cases h
  | succ k ih =>
      intro a0 a h0 h
      simp only [iterUntil] at h
      split at h
      · rename_i hst
        cases h
        exact fun f => ⟨h0 f, O.lfp_le_of_stable a0 hst f⟩
      · exact ih _ a (O.step_le_lfp a0 h0) h

theorem solve_correct (a : List F) (h : O.solve = some a) : ∀ f, f ∈ a ↔ O.lfp f :=
  O.iterUntil_correct _ [] a (fun f hf => by cases hf) h

theorem step_mono (a b : List F) (hab : ∀ x ∈ a, x ∈ b) : ∀ f ∈ O.step a, f ∈ O.step b := by
  intro f hf
  obtain ⟨hu, hs⟩ := (O.mem_step a f).1 hf
  exact (O.mem_step b f).2 ⟨hu, O.spec_mono (fun x hx => hab x hx) f hs⟩

theorem iterUntil_isSome : ∀ (k : Nat) (a : List F), (∀ x ∈ a, x ∈ O.step a) →
    (O.U.filter (fun x => decide (x ∉ a))).length < k → (O.iterUntil k a).isSome = true := by
  intro k
  induction k with
  | zero => intro a _ h; omega
  | succ k ih =>
      intro a hgrow hk
      simp only [iterUntil]
      split
      · rfl
      · rename_i hst
        have hns : ¬ ∀ x ∈ O.step a, x ∈ a := fun hall =>
          hst (List.all_eq_true.2 (fun x hxm => by simpa using hall x hxm))
        have ⟨w, hwS, hwa⟩ : ∃ w, w ∈ O.step a ∧ w ∉ a :=
          Classical.byContradiction (fun hne => hns (fun x hxm =>
            Classical.byContradiction (fun hxa => hne ⟨x, hxm, hxa⟩)))
        have hwU : w ∈ O.U := ((O.mem_step a w).1 hwS).1
        have hlt := filter_length_lt (fun x => decide (x ∉ a)) (fun x => decide (x ∉ O.step a))
          (fun x hq => by
            simp only [decide_eq_true_eq] at hq ⊢
            exact fun hxa => hq (hgrow x hxa))
          w (by simpa using hwa) (by simpa using hwS) O.U hwU
        exact ih _ (O.step_mono _ _ hgrow) (by omega)

theorem solve_isSome : O.solve.isSome = true := by
  refine O.iterUntil_isSome _ [] (fun x h => by cases h) ?_
  have := List.length_filter_le (fun x => decide (x ∉ ([] : List F))) O.U
  omega

/-- Certificate: stages, each inside one round of the previous one. -/
def chainB : List F → List (List F) → Bool
  | _, [] => true
  | prev, next :: rest => next.all (fun f => decide (f ∈ O.step prev)) && chainB next rest

theorem chain_sound : ∀ (stages : List (List F)) (prev : List F), (∀ f ∈ prev, O.lfp f) →
    O.chainB prev stages = true → ∀ a ∈ stages, ∀ f ∈ a, O.lfp f := by
  intro stages
  induction stages with
  | nil => intro _ _ _ a ha; cases ha
  | cons next rest ih =>
      intro prev hprev hc a ha
      simp only [chainB, Bool.and_eq_true] at hc
      have hnext : ∀ f ∈ next, O.lfp f := fun f hf =>
        O.step_le_lfp prev hprev f (by simpa using List.all_eq_true.1 hc.1 f hf)
      cases List.mem_cons.1 ha with
      | inl e => subst e; exact hnext
      | inr m => exact ih next hnext hc.2 a m

theorem lfp_of_chain (stages : List (List F)) (h : O.chainB [] stages = true)
    (a : List F) (ha : a ∈ stages) (f : F) (hf : f ∈ a) : O.lfp f :=
  O.chain_sound stages [] (fun f hf => by cases hf) h a ha f hf

end FinOp
end ShapesCore
