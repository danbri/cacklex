/-
The duality principle, KR 2026 Proposition 1, for one stratum:

    α LFP-conforms to C   iff   Ω \ α GFP-conforms to the dual of C.

Proved here for the full stratum syntax, that is with counting over paths and
ShEx neighbourhood shapes, not only for SSL. Classical logic is used.
-/
import ShapesCore.Fixpoint

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N]

omit [DecidableEq N] in
theorem atomSat_not (I : E → N → Prop) (pos : Bool) (e : E) (v : N) :
    atomSat I (!pos) e v ↔ ¬ atomSat I pos e v := by
  cases pos <;> simp [atomSat]

omit [DecidableEq N] in
theorem compl_compl_iff (α : Asg S N) (s : S) (v : N) : α.compl.compl s v ↔ α s v := by
  simp [Asg.compl]

omit [DecidableEq N] in
theorem TE.Matches.congr {ok ok' : Target S E → N → Prop} (h : ∀ t u, ok t u ↔ ok' t u)
    (e : TE P S E) (l : List (Step P × N)) : TE.Matches ok e l ↔ TE.Matches ok' e l :=
  ⟨TE.Matches.mono (fun t u => (h t u).1), TE.Matches.mono (fun t u => (h t u).2)⟩

omit [DecidableEq N] in
theorem okOf_congr (I : E → N → Prop) {α β : Asg S N} (h : ∀ s v, α s v ↔ β s v) :
    ∀ (t : Target S E) (u : N), okOf I α t u ↔ okOf I β t u := by
  intro t u
  cases t with
  | name s => exact h s u
  | atom pos e => exact Iff.rfl

/-- A node satisfies the dual shape under the complement assignment exactly
    when it fails the shape under the assignment. -/
theorem sat_dual (G : Graph N P) (I : E → N → Prop) (α : Asg S N) (φ : Shape P S E) :
    ∀ v, sat G I α.compl φ.dual v ↔ ¬ sat G I α φ v := by
  induction φ with
  | top => intro v; simp [Shape.dual, sat]
  | bot => intro v; simp [Shape.dual, sat]
  | atom pos e => intro v; simpa [Shape.dual, sat] using atomSat_not I pos e v
  | ref s => intro v; simp [Shape.dual, sat, Asg.compl]
  | and a b iha ihb =>
      intro v
      simp only [Shape.dual, sat, iha v, ihb v]
      exact (Classical.not_and_iff_not_or_not).symm
  | or a b iha ihb =>
      intro v
      simp only [Shape.dual, sat, iha v, ihb v]
      exact not_or.symm
  | geq n π φ ih =>
      intro v
      cases n with
      | zero =>
          simp only [Shape.dual, sat]
          constructor
          · intro hf; exact hf.elim
          · intro hn; exact hn ⟨[], List.nodup_nil, Nat.le_refl _, fun u hu => by cases hu⟩
      | succ n =>
          simp only [Shape.dual, sat]
          constructor
          · intro h ⟨l, hnd, hlen, hall⟩
            have := h l hnd (fun u hu => ⟨(hall u hu).1, fun hd => (ih u).1 hd (hall u hu).2⟩)
            omega
          · intro h l hnd hall
            apply Classical.byContradiction
            intro hlt
            apply h
            refine ⟨l, hnd, by omega, fun u hu => ⟨(hall u hu).1, ?_⟩⟩
            apply Classical.byContradiction
            intro hns
            exact (hall u hu).2 ((ih u).2 hns)
  | amn n π φ ih =>
      intro v
      simp only [Shape.dual, sat]
      constructor
      · intro ⟨l, hnd, hlen, hall⟩ h
        have := h l hnd (fun u hu => ⟨(hall u hu).1, (ih u).1 (hall u hu).2⟩)
        omega
      · intro h
        apply Classical.byContradiction
        intro hne
        apply h
        intro l hnd hall
        apply Classical.byContradiction
        intro hlt
        apply hne
        exact ⟨l, hnd, by omega, fun u hu => ⟨(hall u hu).1, (ih u).2 (hall u hu).2⟩⟩
  | neigh e =>
      intro v
      simp only [Shape.dual, sat]
      exact not_congr (TE.Matches.congr (okOf_congr I (compl_compl_iff α)) e _)
  | nneigh e =>
      intro v
      simp only [Shape.dual, sat]
      exact (Classical.not_not).symm

/-- The dual operator on complements is the complement of the operator. -/
theorem T_dual (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) (α : Asg S N)
    (s : S) (v : N) : T G I C.dual α.compl s v ↔ ¬ T G I C α s v :=
  sat_dual G I α (C s) v

/-- KR 2026 Proposition 1, one stratum: LFP of a catalogue is the complement
    of GFP of its dual. -/
theorem lfp_iff_not_gfp_dual (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    (s : S) (v : N) : lfp G I C s v ↔ ¬ gfp G I C.dual s v := by
  constructor
  · intro hl ⟨β, hβ, hb⟩
    have hpre : (T G I C β.compl).le β.compl := by
      intro s' v' ht hb'
      have h1 := hβ s' v' hb'
      have h2 : T G I C.dual β.compl.compl s' v' :=
        (sat_congr G I (compl_compl_iff β) _ _).2 h1
      exact (T_dual G I C β.compl s' v').1 h2 ht
    exact hl β.compl hpre hb
  · intro hng
    apply Classical.byContradiction
    intro hnl
    apply hng
    refine ⟨(lfp G I C).compl, ?_, hnl⟩
    intro s' v' hc
    exact (T_dual G I C (lfp G I C) s' v').2 (fun ht => hc (T_lfp_le G I C s' v' ht))

/-- The same statement read from the GFP side. -/
theorem gfp_dual_iff_not_lfp (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    (s : S) (v : N) : gfp G I C.dual s v ↔ ¬ lfp G I C s v := by
  rw [lfp_iff_not_gfp_dual]; exact (Classical.not_not).symm

end ShapesCore
