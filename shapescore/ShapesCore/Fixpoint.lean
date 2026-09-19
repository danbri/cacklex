/-
The operator of a catalogue and the three recursive semantics of KR 2026
section 2.3: supported models (SMS), least fixpoint (LFP), greatest fixpoint
(GFP). Assignments are predicates, so Knaster–Tarski is proved directly with
no finiteness assumption.
-/
import ShapesCore.Semantics

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N]

/-- The operator `α ↦ {(s, v) | v ∈ ⟦C(s)⟧^α}`. -/
def T (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) (α : Asg S N) : Asg S N :=
  fun s v => sat G I α (C s) v

theorem T_mono (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    {α β : Asg S N} (h : α.le β) : (T G I C α).le (T G I C β) :=
  fun s v hs => sat_mono G I h (C s) v hs

/-- SMS: an assignment is correct when it is a fixpoint of the operator. -/
def Correct (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) (α : Asg S N) : Prop :=
  ∀ s v, α s v ↔ T G I C α s v

/-- LFP: the intersection of all pre-fixpoints. -/
def lfp (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) : Asg S N :=
  fun s v => ∀ α : Asg S N, (T G I C α).le α → α s v

/-- GFP: the union of all post-fixpoints. -/
def gfp (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) : Asg S N :=
  fun s v => ∃ α : Asg S N, α.le (T G I C α) ∧ α s v

theorem lfp_le_of_prefixed (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    {α : Asg S N} (h : (T G I C α).le α) : (lfp G I C).le α :=
  fun _ _ hl => hl α h

theorem le_gfp_of_postfixed (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    {α : Asg S N} (h : α.le (T G I C α)) : α.le (gfp G I C) :=
  fun _ _ ha => ⟨α, h, ha⟩

theorem T_lfp_le (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) :
    (T G I C (lfp G I C)).le (lfp G I C) := by
  intro s v hs α hα
  exact hα s v (T_mono G I C (lfp_le_of_prefixed G I C hα) s v hs)

theorem gfp_le_T (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) :
    (gfp G I C).le (T G I C (gfp G I C)) := by
  intro s v hg
  obtain ⟨α, hα, ha⟩ := hg
  exact T_mono G I C (le_gfp_of_postfixed G I C hα) s v (hα s v ha)

/-- LFP is a correct assignment. -/
theorem lfp_correct (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) :
    Correct G I C (lfp G I C) := by
  intro s v
  constructor
  · intro hl
    exact hl (T G I C (lfp G I C)) (T_mono G I C (T_lfp_le G I C))
  · exact T_lfp_le G I C s v

/-- GFP is a correct assignment. -/
theorem gfp_correct (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E) :
    Correct G I C (gfp G I C) := by
  intro s v
  constructor
  · exact gfp_le_T G I C s v
  · intro ht
    exact ⟨T G I C (gfp G I C), T_mono G I C (gfp_le_T G I C), ht⟩

/-- Every correct (SMS) assignment lies between LFP and GFP. -/
theorem correct_between (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    {α : Asg S N} (h : Correct G I C α) : (lfp G I C).le α ∧ α.le (gfp G I C) :=
  ⟨lfp_le_of_prefixed G I C (fun s v ht => (h s v).2 ht),
   le_gfp_of_postfixed G I C (fun s v ha => (h s v).1 ha)⟩

/-- So a verdict on which LFP and GFP agree is the verdict of every SMS
    assignment, brave or cautious. -/
theorem sms_determined (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    {α : Asg S N} (h : Correct G I C α) (s : S) (v : N)
    (agree : gfp G I C s v → lfp G I C s v) : α s v ↔ lfp G I C s v :=
  ⟨fun ha => agree ((correct_between G I C h).2 s v ha),
   fun hl => (correct_between G I C h).1 s v hl⟩

end ShapesCore
