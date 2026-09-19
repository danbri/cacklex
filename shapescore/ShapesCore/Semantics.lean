/-
Satisfaction relative to a shape assignment (KR 2026 Table 1, extended with
Definitions 5 and 6), and its monotonicity.
-/
import ShapesCore.Syntax

namespace ShapesCore

/-- A shape assignment: which names hold at which nodes. -/
abbrev Asg (S N : Type) := S → N → Prop

def Asg.le {S N : Type} (α β : Asg S N) : Prop := ∀ s v, α s v → β s v
def Asg.compl {S N : Type} (α : Asg S N) : Asg S N := fun s v => ¬ α s v

def atomSat {N E : Type} (I : E → N → Prop) (pos : Bool) (e : E) (v : N) : Prop :=
  if pos then I e v else ¬ I e v

/-- The node test a triple constraint applies to the far end of an arc. -/
def okOf {N S E : Type} (I : E → N → Prop) (α : Asg S N) : Target S E → N → Prop
  | .name s, u => α s u
  | .atom pos e, u => atomSat I pos e u

/-- A triple expression matches a bag of arcs, given as a list up to
    permutation. `seq` and `star` split the bag into disjoint parts, which is
    why ShEx counts triples where SHACL counts nodes. -/
inductive TE.Matches {N P S E : Type} (ok : Target S E → N → Prop) :
    TE P S E → List (Step P × N) → Prop where
  | eps : Matches ok .eps []
  | tc {st : Step P} {t : Target S E} {u : N} : ok t u → Matches ok (.tc st t) [(st, u)]
  | any {Q : List (Step P)} {st : Step P} {u : N} : st ∉ Q → Matches ok (.anyExcept Q) [(st, u)]
  | seq {a b : TE P S E} {l l1 l2 : List (Step P × N)} :
      Matches ok a l1 → Matches ok b l2 → l.Perm (l1 ++ l2) → Matches ok (.seq a b) l
  | altL {a b : TE P S E} {l : List (Step P × N)} : Matches ok a l → Matches ok (.alt a b) l
  | altR {a b : TE P S E} {l : List (Step P × N)} : Matches ok b l → Matches ok (.alt a b) l
  | starNil {a : TE P S E} : Matches ok (.star a) []
  | starCons {a : TE P S E} {l l1 l2 : List (Step P × N)} :
      Matches ok a l1 → Matches ok (.star a) l2 → l.Perm (l1 ++ l2) → Matches ok (.star a) l

theorem TE.Matches.mono {N P S E : Type} {ok ok' : Target S E → N → Prop}
    (h : ∀ t u, ok t u → ok' t u) {e : TE P S E} {l : List (Step P × N)}
    (m : TE.Matches ok e l) : TE.Matches ok' e l := by
  induction m with
  | eps => exact .eps
  | tc hk => exact .tc (h _ _ hk)
  | any hq => exact .any hq
  | seq _ _ hp iha ihb => exact .seq iha ihb hp
  | altL _ ih => exact .altL ih
  | altR _ ih => exact .altR ih
  | starNil => exact .starNil
  | starCons _ _ hp iha ihb => exact .starCons iha ihb hp

/-- `G, v ⊨ φ` under atom interpretation `I` and assignment `α`. -/
def sat {N P S E : Type} [DecidableEq N] (G : Graph N P) (I : E → N → Prop) (α : Asg S N) :
    Shape P S E → N → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom pos e, v => atomSat I pos e v
  | .ref s, v => α s v
  | .and a b, v => sat G I α a v ∧ sat G I α b v
  | .or a b, v => sat G I α a v ∨ sat G I α b v
  | .geq n π φ, v =>
      ∃ l : List N, l.Nodup ∧ n ≤ l.length ∧ ∀ u ∈ l, Path.Rel G π v u ∧ sat G I α φ u
  | .amn n π φ, v =>
      ∀ l : List N, l.Nodup → (∀ u ∈ l, Path.Rel G π v u ∧ ¬ sat G I α φ u) → l.length ≤ n
  | .neigh e, v => TE.Matches (okOf I α) e (G.nbhd v)
  | .nneigh e, v => ¬ TE.Matches (okOf I α.compl) e (G.nbhd v)

theorem okOf_mono {N S E : Type} (I : E → N → Prop) {α β : Asg S N} (h : α.le β) :
    ∀ t u, okOf I α t u → okOf I β t u := by
  intro t u hk
  cases t with
  | name s => exact h s u hk
  | atom pos e => exact hk

/-- Every shape of the stratum syntax is monotone in the assignment. -/
theorem sat_mono {N P S E : Type} [DecidableEq N] (G : Graph N P) (I : E → N → Prop)
    {α β : Asg S N} (h : α.le β) (φ : Shape P S E) :
    ∀ v, sat G I α φ v → sat G I β φ v := by
  induction φ with
  | top => intro v _; trivial
  | bot => intro v hf; exact hf
  | atom pos e => intro v hs; exact hs
  | ref s => intro v hs; exact h s v hs
  | and a b iha ihb => intro v hs; exact ⟨iha v hs.1, ihb v hs.2⟩
  | or a b iha ihb =>
      intro v hs
      cases hs with
      | inl ha => exact Or.inl (iha v ha)
      | inr hb => exact Or.inr (ihb v hb)
  | geq n π φ ih =>
      intro v hs
      obtain ⟨l, hnd, hlen, hall⟩ := hs
      exact ⟨l, hnd, hlen, fun u hu => ⟨(hall u hu).1, ih u (hall u hu).2⟩⟩
  | amn n π φ ih =>
      intro v hs l hnd hall
      exact hs l hnd (fun u hu => ⟨(hall u hu).1, fun hα => (hall u hu).2 (ih u hα)⟩)
  | neigh e => intro v hs; exact TE.Matches.mono (okOf_mono I h) hs
  | nneigh e =>
      intro v hs hm
      apply hs
      refine TE.Matches.mono (okOf_mono I ?_) hm
      intro s u hb ha
      exact hb (h s u ha)

theorem sat_congr {N P S E : Type} [DecidableEq N] (G : Graph N P) (I : E → N → Prop)
    {α β : Asg S N} (h : ∀ s v, α s v ↔ β s v) (φ : Shape P S E) (v : N) :
    sat G I α φ v ↔ sat G I β φ v :=
  ⟨sat_mono G I (fun s v => (h s v).1) φ v, sat_mono G I (fun s v => (h s v).2) φ v⟩

end ShapesCore
