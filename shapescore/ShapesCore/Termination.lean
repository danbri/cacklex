/-
The solver always answers: `solveLfp_isSome`.

Iterates from the empty assignment grow (`a ⊆ step a` is preserved because the
operator is monotone). An unstable round derives a pair not yet present, so
the number of listed pairs still missing drops. The measure is a filter
length over the fixed pair list, so no duplicate-freeness is needed anywhere.
-/
import ShapesCore.Certificate

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N] [DecidableEq P] [DecidableEq S]

theorem filter_length_le {α : Type} (p q : α → Bool) (hpq : ∀ x, q x = true → p x = true) :
    ∀ U : List α, (U.filter q).length ≤ (U.filter p).length := by
  intro U
  induction U with
  | nil => simp
  | cons x r ih =>
      cases hq : q x with
      | false => cases hp : p x <;> simp [hq, hp] <;> omega
      | true => have hp := hpq x hq; simp [hq, hp]; omega

theorem filter_length_lt {α : Type} (p q : α → Bool) (hpq : ∀ x, q x = true → p x = true)
    (w : α) (hpw : p w = true) (hqw : q w = false) :
    ∀ U : List α, w ∈ U → (U.filter q).length < (U.filter p).length := by
  intro U
  induction U with
  | nil => intro h; cases h
  | cons x r ih =>
      intro hw
      have hle := filter_length_le p q hpq r
      cases List.mem_cons.1 hw with
      | inl e =>
          subst e
          simp [hpw, hqw]; omega
      | inr m =>
          have := ih m
          cases hq : q x with
          | false => cases hp : p x <;> simp [hq, hp] <;> omega
          | true => have hp := hpq x hq; simp [hq, hp]; omega

omit [DecidableEq N] [DecidableEq S] in
theorem mem_pairs (names : List S) (nodes : List N) (s : S) (v : N) :
    (s, v) ∈ pairs names nodes ↔ s ∈ names ∧ v ∈ nodes := by
  simp [pairs]

/-- Listed pairs not yet in `a`. -/
def missing (U : List (S × N)) (a : FAsg S N) : Nat := (U.filter (fun x => decide (x ∉ a))).length

section
variable (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
  (names : List S) (nodes : List N) (hx : ∀ s, (C s).Exec)

include hx in
theorem stepB_mono (a b : FAsg S N) (hab : ∀ x ∈ a, x ∈ b) :
    ∀ x ∈ stepB G Ib C names nodes a, x ∈ stepB G Ib C names nodes b := by
  intro ⟨s, v⟩ hm
  obtain ⟨hs, hv, hb⟩ := (mem_stepB G Ib C names nodes a s v).1 hm
  refine (mem_stepB G Ib C names nodes b s v).2 ⟨hs, hv, ?_⟩
  have h1 := (evalB_iff G Ib a (C s) (hx s) v).1 hb
  exact (evalB_iff G Ib b (C s) (hx s) v).2
    (sat_mono G _ (fun s' v' h => hab (s', v') h) (C s) v h1)

include hx in
theorem iterUntil_isSome : ∀ (k : Nat) (a : FAsg S N),
    (∀ x ∈ a, x ∈ stepB G Ib C names nodes a) → missing (pairs names nodes) a < k →
    (iterUntil G Ib C names nodes k a).isSome = true := by
  intro k
  induction k with
  | zero => intro a _ h; omega
  | succ k ih =>
      intro a hgrow hk
      simp only [iterUntil]
      split
      · rfl
      · rename_i hst
        have hns : ¬ ∀ x ∈ stepB G Ib C names nodes a, x ∈ a := fun hall =>
          hst (List.all_eq_true.2 (fun x hxm => by simpa using hall x hxm))
        have ⟨w, hwS, hwa⟩ : ∃ w, w ∈ stepB G Ib C names nodes a ∧ w ∉ a :=
          Classical.byContradiction (fun hne => hns (fun x hxm =>
            Classical.byContradiction (fun hxa => hne ⟨x, hxm, hxa⟩)))
        have hwU : w ∈ pairs names nodes := by
          obtain ⟨s, v⟩ := w
          have := (mem_stepB G Ib C names nodes a s v).1 hwS
          exact (mem_pairs names nodes s v).2 ⟨this.1, this.2.1⟩
        have hlt : missing (pairs names nodes) (stepB G Ib C names nodes a)
            < missing (pairs names nodes) a := by
          refine filter_length_lt _ _ ?_ w (by simpa using hwa) (by simpa using hwS) _ hwU
          intro x hq
          simp only [decide_eq_true_eq] at hq ⊢
          exact fun hxa => hq (hgrow x hxa)
        exact ih _ (stepB_mono G Ib C names nodes hx _ _ hgrow) (by omega)

include hx in
/-- The solver always returns an assignment, which by `solveLfp_correct` is
    the least fixpoint on the listed nodes. -/
theorem solveLfp_isSome : (solveLfp G Ib C names nodes).isSome = true := by
  refine iterUntil_isSome G Ib C names nodes hx _ [] (fun x h => by cases h) ?_
  have := List.length_filter_le (fun x => decide (x ∉ ([] : FAsg S N))) (pairs names nodes)
  simp only [missing]
  omega

end
end ShapesCore
