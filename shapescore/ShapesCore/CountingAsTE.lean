/-
SHACL's counting quantifier IS a ShEx triple expression.

    ∃≥n st.t    and    { (st.t){n} ; any* }

hold of the same nodes, on any graph without duplicate triples, under any
assignment. No distinct-predicate restriction is needed: over a single step,
distinct triples and distinct far-end nodes are the same thing, because an RDF
graph is a set. The two languages' counting diverges only over compound paths
and unions of predicates, where one node can be reached by several triples.
-/
import ShapesCore.Frontends

namespace ShapesCore

variable {N P S E : Type}

def TE.anyArc : TE P S E := .anyExcept []

/-- `(st.t){n} ; any*` -/
def TE.geqTE (n : Nat) (st : Step P) (t : Target S E) : TE P S E :=
  .seq (TE.rep (.tc st t) n) (.star TE.anyArc)

def Target.toShape : Target S E → Shape P S E
  | .name s => .ref s
  | .atom pos e => .atom pos e

theorem matches_star_any (ok : Target S E → N → Prop) :
    ∀ l : List (Step P × N), TE.Matches ok (.star (TE.anyArc : TE P S E)) l := by
  intro l
  induction l with
  | nil => exact .starNil
  | cons x r ih =>
      cases x with
      | mk st u =>
          exact .starCons (l1 := [(st, u)]) (.any (by simp)) ih (List.Perm.refl _)

theorem matches_rep_tc (ok : Target S E → N → Prop) (st : Step P) (t : Target S E) :
    ∀ us : List N, (∀ u ∈ us, ok t u) →
      TE.Matches ok (TE.rep (.tc st t) us.length) (us.map (fun u => (st, u))) := by
  intro us
  induction us with
  | nil => intro _; exact .eps
  | cons u r ih =>
      intro h
      exact .seq (l1 := [(st, u)]) (.tc (h u (by simp)))
        (ih (fun w hw => h w (List.mem_cons_of_mem _ hw))) (List.Perm.refl _)

theorem rep_tc_inv (ok : Target S E → N → Prop) (st : Step P) (t : Target S E) :
    ∀ (n : Nat) (l : List (Step P × N)), TE.Matches ok (TE.rep (.tc st t) n) l →
      l.length = n ∧ ∀ x ∈ l, x.1 = st ∧ ok t x.2 := by
  intro n
  induction n with
  | zero =>
      intro l h
      have h' : TE.Matches ok (.eps : TE P S E) l := h
      cases h'
      exact ⟨rfl, fun x hx => by cases hx⟩
  | succ n ih =>
      intro l h
      have h' : TE.Matches ok (.seq (.tc st t) (TE.rep (.tc st t) n)) l := h
      cases h' with
      | seq h1 h2 hp =>
          cases h1 with
          | tc hk =>
              obtain ⟨hlen, hall⟩ := ih _ h2
              refine ⟨by rw [hp.length_eq]; simp [hlen], ?_⟩
              intro x hx
              have hx' := hp.mem_iff.1 hx
              simp only [List.singleton_append, List.mem_cons] at hx'
              cases hx' with
              | inl e => subst e; exact ⟨rfl, hk⟩
              | inr m => exact hall x m

theorem exists_perm_append {α : Type} [DecidableEq α] :
    ∀ (A L : List α), A.Nodup → (∀ x ∈ A, x ∈ L) → ∃ R, L.Perm (A ++ R) := by
  intro A
  induction A with
  | nil => intro L _ _; exact ⟨L, List.Perm.refl _⟩
  | cons x A' ih =>
      intro L hnd hsub
      have hx : x ∈ L := hsub x (by simp)
      have hnd' := List.nodup_cons.1 hnd
      have hsub' : ∀ y ∈ A', y ∈ L.erase x := by
        intro y hy
        have hne : y ≠ x := fun e => hnd'.1 (e ▸ hy)
        exact (List.mem_erase_of_ne hne).2 (hsub y (List.mem_cons_of_mem _ hy))
      obtain ⟨R, hR⟩ := ih (L.erase x) hnd'.2 hsub'
      exact ⟨R, (List.perm_cons_erase hx).trans (List.Perm.cons x hR)⟩

theorem nodup_map_mk (st : Step P) : ∀ us : List N, us.Nodup →
    (us.map (fun u => (st, u))).Nodup := by
  intro us
  induction us with
  | nil => intro _; simp
  | cons u r ih =>
      intro h
      have h' := List.nodup_cons.1 h
      simp only [List.map_cons]
      refine List.nodup_cons.2 ⟨?_, ih h'.2⟩
      intro hm
      obtain ⟨w, hw, he⟩ := List.mem_map.1 hm
      have : w = u := congrArg Prod.snd he
      exact h'.1 (this ▸ hw)

theorem nodup_map_snd (st : Step P) : ∀ l : List (Step P × N), l.Nodup →
    (∀ x ∈ l, x.1 = st) → (l.map (fun x => x.2)).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x r ih =>
      intro h hst
      have h' := List.nodup_cons.1 h
      simp only [List.map_cons]
      refine List.nodup_cons.2 ⟨?_, ih h'.2 (fun y hy => hst y (List.mem_cons_of_mem _ hy))⟩
      intro hm
      obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
      have h1 : y.1 = x.1 := by rw [hst y (List.mem_cons_of_mem _ hy), hst x (by simp)]
      have : y = x := Prod.ext h1 he
      exact h'.1 (this ▸ hy)

/-- The triple expression, on any duplicate-free bag of arcs. -/
theorem geqTE_iff [DecidableEq N] [DecidableEq P] (ok : Target S E → N → Prop) (n : Nat)
    (st : Step P) (t : Target S E) (L : List (Step P × N)) (hL : L.Nodup) :
    TE.Matches ok (TE.geqTE n st t) L ↔
      ∃ us : List N, us.Nodup ∧ us.length = n ∧ ∀ u ∈ us, (st, u) ∈ L ∧ ok t u := by
  constructor
  · intro h
    cases h with
    | @seq _ _ _ l1 l2 h1 _ hp =>
        obtain ⟨hlen, hall⟩ := rep_tc_inv ok st t n l1 h1
        have hnd12 : (l1 ++ l2).Nodup := hp.nodup_iff.1 hL
        have hnd1 : l1.Nodup := (List.nodup_append.1 hnd12).1
        refine ⟨l1.map (fun x => x.2), nodup_map_snd st l1 hnd1 (fun x hx => (hall x hx).1),
          by simp [hlen], ?_⟩
        intro u hu
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
        have hxL : x ∈ L := hp.mem_iff.2 (List.mem_append_left _ hx)
        have hx1 := (hall x hx).1
        refine ⟨?_, (hall x hx).2⟩
        have : x = (st, x.2) := Prod.ext hx1 rfl
        exact this ▸ hxL
  · intro ⟨us, hnd, hlen, hall⟩
    obtain ⟨R, hR⟩ := exists_perm_append (us.map (fun u => (st, u))) L (nodup_map_mk st us hnd)
      (fun x hx => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
        exact (hall u hu).1)
    have hrep := matches_rep_tc ok st t us (fun u hu => (hall u hu).2)
    rw [hlen] at hrep
    exact .seq hrep (matches_star_any ok R) hR

/-! ## From bags of arcs to graphs -/

theorem Graph.mem_nbhd [DecidableEq N] (G : Graph N P) (v : N) (st : Step P) (u : N) :
    (st, u) ∈ G.nbhd v ↔ G.arc v st u := by
  simp only [Graph.nbhd, List.mem_append, List.mem_filterMap]
  cases st with
  | fwd p =>
      simp only [Graph.arc]
      constructor
      · rintro (⟨⟨a, q, b⟩, hm, hs⟩ | ⟨⟨a, q, b⟩, hm, hs⟩)
        · split at hs
          · rename_i h; simp at hs h; obtain ⟨rfl, rfl⟩ := hs; subst h; exact hm
          · cases hs
        · split at hs
          · simp at hs
          · cases hs
      · intro hm; exact Or.inl ⟨(v, p, u), hm, by simp⟩
  | inv p =>
      simp only [Graph.arc]
      constructor
      · rintro (⟨⟨a, q, b⟩, hm, hs⟩ | ⟨⟨a, q, b⟩, hm, hs⟩)
        · split at hs
          · simp at hs
          · cases hs
        · split at hs
          · rename_i h; simp at hs h; obtain ⟨rfl, rfl⟩ := hs; subst h; exact hm
          · cases hs
      · intro hm; exact Or.inr ⟨(u, p, v), hm, by simp⟩

theorem nodup_filterMap {α β : Type} (f : α → Option β)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b) :
    ∀ l : List α, l.Nodup → (l.filterMap f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a r ih =>
      intro h
      have h' := List.nodup_cons.1 h
      cases hfa : f a with
      | none => simpa [List.filterMap_cons, hfa] using ih h'.2
      | some c =>
          simp only [List.filterMap_cons, hfa]
          refine List.nodup_cons.2 ⟨?_, ih h'.2⟩
          intro hm
          obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.1 hm
          exact h'.1 ((hinj a b c hfa hfb) ▸ hb)

theorem ite_some {α : Type} {c : Prop} [Decidable c] {x y : α}
    (h : (if c then some x else none) = some y) : c ∧ x = y := by
  by_cases hc : c
  · simp [hc] at h; exact ⟨hc, h⟩
  · simp [hc] at h

theorem Graph.nodup_nbhd [DecidableEq N] (G : Graph N P) (hG : G.triples.Nodup) (v : N) :
    (G.nbhd v).Nodup := by
  simp only [Graph.nbhd]
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · refine nodup_filterMap _ ?_ _ hG
    intro a b c ha hb
    obtain ⟨h1, e1⟩ := ite_some ha
    obtain ⟨h2, e2⟩ := ite_some hb
    have e := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext (h1.trans h2.symm) (Prod.ext (Step.fwd.inj e.1) e.2)
  · refine nodup_filterMap _ ?_ _ hG
    intro a b c ha hb
    obtain ⟨h1, e1⟩ := ite_some ha
    obtain ⟨h2, e2⟩ := ite_some hb
    have e := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext e.2 (Prod.ext (Step.inv.inj e.1) (h1.trans h2.symm))
  · intro x hx y hy hxy
    subst hxy
    obtain ⟨a, _, ha⟩ := List.mem_filterMap.1 hx
    obtain ⟨b, _, hb⟩ := List.mem_filterMap.1 hy
    obtain ⟨_, e1⟩ := ite_some ha
    obtain ⟨_, e2⟩ := ite_some hb
    have e := (Prod.mk.inj (e1.trans e2.symm)).1
    cases e

/-- SHACL counting over one step and the ShEx triple expression agree. -/
theorem sat_geq_iff_neigh [DecidableEq N] [DecidableEq P] (G : Graph N P) (hG : G.triples.Nodup)
    (I : E → N → Prop) (α : Asg S N) (n : Nat) (st : Step P) (t : Target S E) (v : N) :
    sat G I α (.geq n (.step st) t.toShape) v ↔ sat G I α (.neigh (TE.geqTE n st t)) v := by
  have hok : ∀ u, sat G I α (t.toShape : Shape P S E) u ↔ okOf I α t u := by
    intro u; cases t <;> simp [Target.toShape, sat, okOf]
  simp only [sat]
  rw [geqTE_iff (okOf I α) n st t (G.nbhd v) (G.nodup_nbhd hG v)]
  constructor
  · intro ⟨l, hnd, hlen, hall⟩
    refine ⟨l.take n, hnd.sublist (List.take_sublist n l), by simp; omega, ?_⟩
    intro u hu
    have hul := List.mem_of_mem_take hu
    exact ⟨(G.mem_nbhd v st u).2 ((Path.rel_step_iff G st v u).1 (hall u hul).1),
      (hok u).1 (hall u hul).2⟩
  · intro ⟨us, hnd, hlen, hall⟩
    exact ⟨us, hnd, by omega, fun u hu =>
      ⟨.step ((G.mem_nbhd v st u).1 (hall u hu).1), (hok u).2 (hall u hu).2⟩⟩

end ShapesCore
