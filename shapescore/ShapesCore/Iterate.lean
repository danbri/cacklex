/-
Kleene iteration for LFP on a finite graph, and GFP through duality.

`solveLfp` iterates the catalogue's operator from the empty assignment until
it stabilises, within a fuel bound of one round per (name, node) pair. If it
returns an assignment, that assignment IS the least fixpoint on the listed
nodes (`solveLfp_correct`). `Termination.lean` proves the fuel always suffices,
so it always returns one.
-/
import ShapesCore.Exec

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N] [DecidableEq P] [DecidableEq S]

/-- One round of the operator, restricted to the listed names and nodes. -/
def stepB (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (a : FAsg S N) : FAsg S N :=
  names.flatMap fun s => nodes.filterMap fun v => if evalB G Ib a (C s) v then some (s, v) else none

theorem mem_stepB (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (a : FAsg S N) (s : S) (v : N) :
    (s, v) ∈ stepB G Ib C names nodes a ↔ s ∈ names ∧ v ∈ nodes ∧ evalB G Ib a (C s) v = true := by
  simp only [stepB, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨s', hs', v', hv', h⟩
    split at h
    · rename_i hb
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs', hv', hb⟩
    · cases h
  · rintro ⟨hs, hv, hb⟩
    exact ⟨s, hs, v, hv, by simp [hb]⟩

/-- `a` is closed under the operator: nothing new is derived. -/
def stableB (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (a : FAsg S N) : Bool :=
  (stepB G Ib C names nodes a).all (fun x => decide (x ∈ a))

def iterUntil (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) : Nat → FAsg S N → Option (FAsg S N)
  | 0, _ => none
  | k+1, a => if stableB G Ib C names nodes a then some a
              else iterUntil G Ib C names nodes k (stepB G Ib C names nodes a)

/-- Every (name, node) pair the solver can ever derive. -/
def pairs (names : List S) (nodes : List N) : List (S × N) :=
  names.flatMap fun s => nodes.map fun v => (s, v)

def solveLfp (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) : Option (FAsg S N) :=
  iterUntil G Ib C names nodes ((pairs names nodes).length + 1) []

/-- Every endpoint of every triple is listed. -/
def Graph.ClosedIn (G : Graph N P) (nodes : List N) : Prop :=
  ∀ t ∈ G.triples, t.1 ∈ nodes ∧ t.2.2 ∈ nodes

omit [DecidableEq P] [DecidableEq S] in
/-- On the executable fragment, satisfaction at a listed node looks at the
    assignment only on listed nodes. -/
theorem sat_local (G : Graph N P) (I : E → N → Prop) (nodes : List N) (hcl : G.ClosedIn nodes)
    {α β : Asg S N} (h : ∀ s u, u ∈ nodes → α s u → β s u) (φ : Shape P S E) (hx : φ.Exec) :
    ∀ v, v ∈ nodes → sat G I α φ v → sat G I β φ v := by
  have reach : ∀ (st : Step P) (v u : N), Path.Rel G (.step st) v u → u ∈ nodes := by
    intro st v u hr
    have harc := (Path.rel_step_iff G st v u).1 hr
    cases st with
    | fwd p => exact (hcl _ harc).2
    | inv p => exact (hcl _ harc).1
  induction φ with
  | top => intro v _ _; trivial
  | bot => intro v _ hf; exact hf
  | atom pos e => intro v _ hs; exact hs
  | ref s => intro v hv hs; exact h s v hv hs
  | and x y ihx ihy => intro v hv hs; exact ⟨ihx hx.1 v hv hs.1, ihy hx.2 v hv hs.2⟩
  | or x y ihx ihy =>
      intro v hv hs
      cases hs with
      | inl ha => exact Or.inl (ihx hx.1 v hv ha)
      | inr hb => exact Or.inr (ihy hx.2 v hv hb)
  | geq n π φ ih =>
      cases π with
      | step st =>
          intro v _ ⟨l, hnd, hlen, hall⟩
          exact ⟨l, hnd, hlen, fun u hu =>
            ⟨(hall u hu).1, ih hx u (reach st v u (hall u hu).1) (hall u hu).2⟩⟩
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | amn n π φ ih =>
      cases π with
      | step st =>
          intro v _ hs l hnd hall
          exact hs l hnd (fun u hu =>
            ⟨(hall u hu).1, fun hα => (hall u hu).2 (ih hx u (reach st v u (hall u hu).1) hα)⟩)
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

section
variable (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
  (names : List S) (nodes : List N) (hx : ∀ s, (C s).Exec)

local notation "I'" => (fun (e : E) (v : N) => Ib e v = true)

include hx in
/-- One round keeps an assignment below LFP. -/
theorem stepB_le_lfp (a : FAsg S N) (ha : a.toAsg.le (lfp G I' C)) :
    (stepB G Ib C names nodes a).toAsg.le (lfp G I' C) := by
  intro s v hm
  have hb := ((mem_stepB G Ib C names nodes a s v).1 hm).2.2
  have hs := (evalB_iff G Ib a (C s) (hx s) v).1 hb
  exact T_lfp_le G I' C s v (sat_mono G I' ha (C s) v hs)

include hx in
/-- A stable assignment below LFP contains LFP on the listed nodes. -/
theorem lfp_le_of_stable (hnames : ∀ s, s ∈ names) (hcl : G.ClosedIn nodes) (a : FAsg S N)
    (ha : a.toAsg.le (lfp G I' C)) (hst : stableB G Ib C names nodes a = true) :
    ∀ s v, v ∈ nodes → lfp G I' C s v → (s, v) ∈ a := by
  intro s v hv hl
  let α' : Asg S N := fun s v => (s, v) ∈ a ∨ (v ∉ nodes ∧ lfp G I' C s v)
  have hα'le : α'.le (lfp G I' C) := by
    intro s v h
    cases h with
    | inl h => exact ha s v h
    | inr h => exact h.2
  have hpre : (T G I' C α').le α' := by
    intro s v ht
    by_cases hvn : v ∈ nodes
    · left
      have hloc : sat G I' a.toAsg (C s) v :=
        sat_local G I' nodes hcl (fun s u hu h => by
          cases h with
          | inl h => exact h
          | inr h => exact absurd hu h.1) (C s) (hx s) v hvn ht
      have hb := (evalB_iff G Ib a (C s) (hx s) v).2 hloc
      have hm := (mem_stepB G Ib C names nodes a s v).2 ⟨hnames s, hvn, hb⟩
      have := List.all_eq_true.1 hst (s, v) hm
      simpa using this
    · right
      exact ⟨hvn, T_lfp_le G I' C s v (T_mono G I' C hα'le s v ht)⟩
  cases hl α' hpre with
  | inl h => exact h
  | inr h => exact absurd hv h.1

include hx in
theorem iterUntil_correct (hnames : ∀ s, s ∈ names) (hcl : G.ClosedIn nodes) :
    ∀ (k : Nat) (a0 a : FAsg S N), a0.toAsg.le (lfp G I' C) →
      iterUntil G Ib C names nodes k a0 = some a →
      ∀ s v, v ∈ nodes → ((s, v) ∈ a ↔ lfp G I' C s v) := by
  intro k
  induction k with
  | zero => intro a0 a _ h; cases h
  | succ k ih =>
      intro a0 a h0 h
      simp only [iterUntil] at h
      split at h
      · rename_i hst
        cases h
        intro s v hv
        exact ⟨fun hm => h0 s v hm,
               lfp_le_of_stable G Ib C names nodes hx hnames hcl a0 h0 hst s v hv⟩
      · exact ih _ a (stepB_le_lfp G Ib C names nodes hx a0 h0) h

include hx in
/-- If the solver answers, the answer is the least fixpoint on the listed nodes. -/
theorem solveLfp_correct (hnames : ∀ s, s ∈ names) (hcl : G.ClosedIn nodes) (a : FAsg S N)
    (h : solveLfp G Ib C names nodes = some a) :
    ∀ s v, v ∈ nodes → ((s, v) ∈ a ↔ lfp G I' C s v) :=
  iterUntil_correct G Ib C names nodes hx hnames hcl _ [] a
    (fun s v hm => by simp [FAsg.toAsg] at hm) h

end

/-! ## GFP through the dual catalogue -/

omit [DecidableEq P] [DecidableEq S] in
theorem sat_dual_dual (G : Graph N P) (I : E → N → Prop) (α : Asg S N) (φ : Shape P S E) (v : N) :
    sat G I α φ.dual.dual v ↔ sat G I α φ v := by
  have h1 := sat_dual G I α.compl φ.dual v
  have h2 := sat_dual G I α φ v
  have h3 := sat_congr G I (compl_compl_iff α) φ.dual.dual v
  rw [← h3, h1, h2]
  exact Classical.not_not

omit [DecidableEq P] [DecidableEq S] in
/-- GFP of a catalogue is the complement of LFP of its dual. -/
theorem gfp_iff_not_lfp_dual (G : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    (s : S) (v : N) : gfp G I C s v ↔ ¬ lfp G I C.dual s v := by
  rw [← gfp_dual_iff_not_lfp G I C.dual s v]
  constructor
  · rintro ⟨α, hα, ha⟩
    exact ⟨α, fun s' v' h => (sat_dual_dual G I α (C s') v').2 (hα s' v' h), ha⟩
  · rintro ⟨α, hα, ha⟩
    exact ⟨α, fun s' v' h => (sat_dual_dual G I α (C s') v').1 (hα s' v' h), ha⟩

omit [DecidableEq N] [DecidableEq P] [DecidableEq S] in
theorem dual_exec (φ : Shape P S E) (hx : φ.Exec) : φ.dual.Exec := by
  induction φ with
  | top => trivial
  | bot => trivial
  | atom _ _ => trivial
  | ref _ => trivial
  | and a b iha ihb => exact ⟨iha hx.1, ihb hx.2⟩
  | or a b iha ihb => exact ⟨iha hx.1, ihb hx.2⟩
  | geq n π φ ih =>
      cases π with
      | step st => cases n with
        | zero => trivial
        | succ n => exact ih hx
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | amn n π φ ih =>
      cases π with
      | step st => exact ih hx
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

/-- Decide one (name, node) pair under LFP or GFP. `none` means out of fuel. -/
def checkLfp (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (s : S) (v : N) : Option Bool :=
  (solveLfp G Ib C names nodes).map (fun a => decide ((s, v) ∈ a))

def checkGfp (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (s : S) (v : N) : Option Bool :=
  (solveLfp G Ib C.dual names nodes).map (fun a => !decide ((s, v) ∈ a))

theorem checkLfp_correct (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (hx : ∀ s, (C s).Exec) (hnames : ∀ s, s ∈ names)
    (hcl : G.ClosedIn nodes) (s : S) (v : N) (hv : v ∈ nodes) (b : Bool)
    (h : checkLfp G Ib C names nodes s v = some b) :
    b = true ↔ lfp G (fun e v => Ib e v = true) C s v := by
  simp only [checkLfp, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  rw [decide_eq_true_eq]
  exact solveLfp_correct G Ib C names nodes hx hnames hcl a ha s v hv

theorem checkGfp_correct (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (names : List S) (nodes : List N) (hx : ∀ s, (C s).Exec) (hnames : ∀ s, s ∈ names)
    (hcl : G.ClosedIn nodes) (s : S) (v : N) (hv : v ∈ nodes) (b : Bool)
    (h : checkGfp G Ib C names nodes s v = some b) :
    b = true ↔ gfp G (fun e v => Ib e v = true) C s v := by
  simp only [checkGfp, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  rw [gfp_iff_not_lfp_dual]
  have := solveLfp_correct G Ib C.dual names nodes (fun s => dual_exec (C s) (hx s)) hnames hcl a ha s v hv
  simp [← this]

end ShapesCore
