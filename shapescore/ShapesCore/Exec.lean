/-
An executable evaluator for the counting fragment, with a proof that it
decides `sat`.

Fragment (`Shape.Exec`): atoms, names, ∧, ∨, and `geq` / `amn` over a single
step. That is SSL plus counting, which is the restricted SHACL of KR 2026
Definition 8 without `∃π.φ` over compound paths. Compound paths and triple
expressions are not covered here.
-/
import ShapesCore.Frontends

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N]

/-! ## Lists as finite sets -/

def dedup : List N → List N
  | [] => []
  | x :: t => if x ∈ dedup t then dedup t else x :: dedup t

theorem mem_dedup (l : List N) (x : N) : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons y t ih =>
      simp only [dedup]
      split
      · rename_i h
        constructor
        · intro hx; exact List.mem_cons_of_mem _ (ih.1 hx)
        · intro hx
          cases List.mem_cons.1 hx with
          | inl e => subst e; exact h
          | inr m => exact ih.2 m
      · simp [ih]

theorem nodup_dedup (l : List N) : (dedup l).Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons y t ih =>
      simp only [dedup]
      split
      · exact ih
      · rename_i h; exact List.nodup_cons.2 ⟨h, ih⟩

/-- Pigeonhole: a duplicate-free list inside `m` is no longer than `m`. -/
theorem length_le_of_nodup_subset : ∀ (l m : List N), l.Nodup → (∀ x ∈ l, x ∈ m) →
    l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intro m _ _; simp
  | cons x t ih =>
      intro m hnd hsub
      have hx : x ∈ m := hsub x (by simp)
      have hnd' := List.nodup_cons.1 hnd
      have hsub' : ∀ y ∈ t, y ∈ m.erase x := by
        intro y hy
        have hne : y ≠ x := fun e => hnd'.1 (e ▸ hy)
        exact (List.mem_erase_of_ne hne).2 (hsub y (List.mem_cons_of_mem _ hy))
      have := ih (m.erase x) hnd'.2 hsub'
      have hlen := List.length_erase_of_mem hx
      have hpos : 0 < m.length := List.length_pos_of_mem hx
      simp only [List.length_cons]
      omega

/-! ## Successors -/

/-- The distinct nodes one step away. -/
def Graph.succ [DecidableEq P] (G : Graph N P) (v : N) : Step P → List N
  | .fwd p => dedup (G.triples.filterMap (fun t => if t.1 = v ∧ t.2.1 = p then some t.2.2 else none))
  | .inv p => dedup (G.triples.filterMap (fun t => if t.2.2 = v ∧ t.2.1 = p then some t.1 else none))

theorem Graph.mem_succ [DecidableEq P] (G : Graph N P) (v : N) (st : Step P) (u : N) :
    u ∈ G.succ v st ↔ G.arc v st u := by
  cases st with
  | fwd p =>
      simp only [Graph.succ, mem_dedup, List.mem_filterMap, Graph.arc]
      constructor
      · rintro ⟨⟨a, q, b⟩, hm, hs⟩
        split at hs
        · rename_i h
          simp at hs h
          obtain ⟨rfl, rfl⟩ := h
          subst hs
          exact hm
        · cases hs
      · intro hm
        exact ⟨(v, p, u), hm, by simp⟩
  | inv p =>
      simp only [Graph.succ, mem_dedup, List.mem_filterMap, Graph.arc]
      constructor
      · rintro ⟨⟨a, q, b⟩, hm, hs⟩
        split at hs
        · rename_i h
          simp at hs h
          obtain ⟨rfl, rfl⟩ := h
          subst hs
          exact hm
        · cases hs
      · intro hm
        exact ⟨(u, p, v), hm, by simp⟩

theorem Graph.nodup_succ [DecidableEq P] (G : Graph N P) (v : N) (st : Step P) :
    (G.succ v st).Nodup := by
  cases st <;> exact nodup_dedup _

/-! ## The evaluator -/

/-- A finite assignment. -/
abbrev FAsg (S N : Type) := List (S × N)

def FAsg.toAsg [DecidableEq S] (a : FAsg S N) : Asg S N := fun s v => (s, v) ∈ a

def Shape.Exec : Shape P S E → Prop
  | .top => True
  | .bot => True
  | .atom _ _ => True
  | .ref _ => True
  | .and a b => a.Exec ∧ b.Exec
  | .or a b => a.Exec ∧ b.Exec
  | .geq _ (.step _) φ => φ.Exec
  | .geq _ _ _ => False
  | .amn _ (.step _) φ => φ.Exec
  | .amn _ _ _ => False
  | .neigh _ => False
  | .nneigh _ => False

def evalB [DecidableEq P] [DecidableEq S] (G : Graph N P) (Ib : E → N → Bool) (a : FAsg S N) :
    Shape P S E → N → Bool
  | .top, _ => true
  | .bot, _ => false
  | .atom pos e, v => if pos then Ib e v else !(Ib e v)
  | .ref s, v => decide ((s, v) ∈ a)
  | .and x y, v => evalB G Ib a x v && evalB G Ib a y v
  | .or x y, v => evalB G Ib a x v || evalB G Ib a y v
  | .geq n (.step st) φ, v => decide (n ≤ ((G.succ v st).filter (fun u => evalB G Ib a φ u)).length)
  | .amn n (.step st) φ, v => decide (((G.succ v st).filter (fun u => !(evalB G Ib a φ u))).length ≤ n)
  | .geq _ _ _, _ => false
  | .amn _ _ _, _ => false
  | .neigh _, _ => false
  | .nneigh _, _ => false

/-- The evaluator decides satisfaction on the executable fragment. -/
theorem evalB_iff [DecidableEq P] [DecidableEq S] (G : Graph N P) (Ib : E → N → Bool)
    (a : FAsg S N) (φ : Shape P S E) (hx : φ.Exec) :
    ∀ v, evalB G Ib a φ v = true ↔ sat G (fun e v => Ib e v = true) a.toAsg φ v := by
  induction φ with
  | top => intro v; simp [evalB, sat]
  | bot => intro v; simp [evalB, sat]
  | atom pos e => intro v; cases pos <;> simp [evalB, sat, atomSat]
  | ref s => intro v; simp [evalB, sat, FAsg.toAsg]
  | and x y ihx ihy => intro v; simp [evalB, sat, ihx hx.1 v, ihy hx.2 v]
  | or x y ihx ihy => intro v; simp [evalB, sat, ihx hx.1 v, ihy hx.2 v]
  | geq n π φ ih =>
      intro v
      cases π with
      | step st =>
          have ih := ih hx
          simp only [evalB, sat, decide_eq_true_eq]
          constructor
          · intro hn
            refine ⟨(G.succ v st).filter (fun u => evalB G Ib a φ u),
              (G.nodup_succ v st).filter _, hn, ?_⟩
            intro u hu
            have := List.mem_filter.1 hu
            exact ⟨.step ((G.mem_succ v st u).1 this.1), (ih u).1 this.2⟩
          · intro ⟨l, hnd, hlen, hall⟩
            have := length_le_of_nodup_subset l _ hnd (fun u hu =>
              List.mem_filter.2 ⟨(G.mem_succ v st u).2 ((Path.rel_step_iff G st v u).1 (hall u hu).1),
                (ih u).2 (hall u hu).2⟩)
            exact Nat.le_trans hlen this
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | amn n π φ ih =>
      intro v
      cases π with
      | step st =>
          have ih := ih hx
          simp only [evalB, sat, decide_eq_true_eq]
          constructor
          · intro hn l hnd hall
            have := length_le_of_nodup_subset l
              ((G.succ v st).filter (fun u => !(evalB G Ib a φ u))) hnd (fun u hu =>
              List.mem_filter.2 ⟨(G.mem_succ v st u).2 ((Path.rel_step_iff G st v u).1 (hall u hu).1), by
                have h2 := (hall u hu).2
                cases hb : evalB G Ib a φ u with
                | false => rfl
                | true => exact absurd ((ih u).1 hb) h2⟩)
            omega
          · intro h
            refine h _ ((G.nodup_succ v st).filter _) ?_
            intro u hu
            have := List.mem_filter.1 hu
            refine ⟨.step ((G.mem_succ v st u).1 this.1), fun hs => ?_⟩
            have hb := (ih u).2 hs
            simp [hb] at this
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

end ShapesCore
