/-
The Simple Shape Language of KR 2026 section 2.2 as a fragment of the stratum
syntax: `∃p.φ` is `geq 1` and `∀p.φ` is `amn 0`. The two lemmas check that the
derived forms have exactly the semantics of the paper's Table 1.
-/
import ShapesCore.Duality

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N]

def Shape.ex (st : Step P) (φ : Shape P S E) : Shape P S E := .geq 1 (.step st) φ
def Shape.all (st : Step P) (φ : Shape P S E) : Shape P S E := .amn 0 (.step st) φ

theorem sat_ex (G : Graph N P) (I : E → N → Prop) (α : Asg S N) (st : Step P)
    (φ : Shape P S E) (v : N) :
    sat G I α (.ex st φ) v ↔ ∃ u, G.arc v st u ∧ sat G I α φ u := by
  simp only [Shape.ex, sat]
  constructor
  · intro ⟨l, _, hlen, hall⟩
    cases l with
    | nil => simp at hlen
    | cons u t =>
        have h := hall u (by simp)
        exact ⟨u, (Path.rel_step_iff G st v u).1 h.1, h.2⟩
  · intro ⟨u, harc, hs⟩
    refine ⟨[u], by simp, by simp, ?_⟩
    intro w hw
    simp at hw
    subst hw
    exact ⟨.step harc, hs⟩

theorem sat_all (G : Graph N P) (I : E → N → Prop) (α : Asg S N) (st : Step P)
    (φ : Shape P S E) (v : N) :
    sat G I α (.all st φ) v ↔ ∀ u, G.arc v st u → sat G I α φ u := by
  simp only [Shape.all, sat]
  constructor
  · intro h u harc
    apply Classical.byContradiction
    intro hns
    have := h [u] (by simp) (by
      intro w hw
      simp at hw
      subst hw
      exact ⟨.step harc, hns⟩)
    simp at this
  · intro h l _ hall
    cases l with
    | nil => simp
    | cons u t =>
        have hu := hall u (by simp)
        exact absurd (h u ((Path.rel_step_iff G st v u).1 hu.1)) hu.2

/-- `∃` and `∀` are dual, as in the paper's definition of the dual shape. -/
theorem dual_ex (st : Step P) (φ : Shape P S E) : (Shape.ex st φ).dual = .all st φ.dual := rfl
theorem dual_all (st : Step P) (φ : Shape P S E) : (Shape.all st φ).dual = .ex st φ.dual := rfl

end ShapesCore
