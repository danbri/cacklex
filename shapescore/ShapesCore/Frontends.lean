/-
How SHACL and ShEx surface syntax lands in the core. These are definitions,
with the one theorem needed to justify the SHACL upper bound.

SHACL (KR 2026 Definition 5; SHACL 1.2 Core):
  sh:minCount n on path π with sh:node/qualified shape φ   geq n π φ
  sh:maxCount n ... (φ must not mention this stratum)      leq n π φ
  sh:closed, sh:equals, sh:disjoint, node tests,
  sh:class, datatype lists, sh:nodeKind                    atoms (see below)
  sh:and / sh:or / sh:not                                  and / or / dual on closed φ
  sh:node to a shape of this stratum                       ref s

ShEx (KR 2026 Definition 6; ShEx 2.1 and the shex-next EXTENDS work):
  { e }  closed on outgoing arcs                           halfOpen e
  { e }  ordinary open shape                               openShape e Q
  e?  e{m,n}                                               opt, rep
  node constraints                                         atoms
  @<S> inside a triple constraint                          Target.name s
-/
import ShapesCore.SSL

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N]

/-! ## Atoms that do not depend on the assignment -/

/-- SHACL `closed(Q)`: no outgoing predicate outside `Q`. -/
def closedI (G : Graph N P) (Q : List P) (v : N) : Prop :=
  ∀ p u, (v, p, u) ∈ G.triples → p ∈ Q

/-- SHACL `eq(π, p)`. -/
def eqI (G : Graph N P) (π : Path P) (p : P) (v : N) : Prop :=
  ∀ u, Path.Rel G π v u ↔ (v, p, u) ∈ G.triples

/-- SHACL `disj(π, p)`. -/
def disjI (G : Graph N P) (π : Path P) (p : P) (v : N) : Prop :=
  ∀ u, ¬ (Path.Rel G π v u ∧ (v, p, u) ∈ G.triples)

/-! ## Shapes that do not mention the current stratum -/

def TE.NameFree : TE P S E → Prop
  | .eps => True
  | .tc _ (.name _) => False
  | .tc _ (.atom _ _) => True
  | .anyExcept _ => True
  | .seq a b => a.NameFree ∧ b.NameFree
  | .alt a b => a.NameFree ∧ b.NameFree
  | .star a => a.NameFree

def Shape.Closed : Shape P S E → Prop
  | .top => True
  | .bot => True
  | .atom _ _ => True
  | .ref _ => False
  | .and a b => a.Closed ∧ b.Closed
  | .or a b => a.Closed ∧ b.Closed
  | .geq _ _ φ => φ.Closed
  | .amn _ _ φ => φ.Closed
  | .neigh e => e.NameFree
  | .nneigh e => e.NameFree

omit [DecidableEq N] in
theorem TE.Matches.of_nameFree (I : E → N → Prop) (α β : Asg S N) {e : TE P S E}
    {l : List (Step P × N)} (m : TE.Matches (okOf I α) e l) (hf : e.NameFree) :
    TE.Matches (okOf I β) e l := by
  induction m with
  | eps => exact .eps
  | @tc st t u hk =>
      cases t with
      | name s => exact hf.elim
      | atom pos e => exact .tc hk
  | any hq => exact .any hq
  | seq _ _ hp iha ihb => exact .seq (iha hf.1) (ihb hf.2) hp
  | altL _ ih => exact .altL (ih hf.1)
  | altR _ ih => exact .altR (ih hf.2)
  | starNil => exact .starNil
  | starCons _ _ hp iha ihb => exact .starCons (iha hf) (ihb hf) hp

/-- A closed shape means the same under every assignment. -/
theorem sat_closed (G : Graph N P) (I : E → N → Prop) (α β : Asg S N) (φ : Shape P S E)
    (hc : φ.Closed) : ∀ v, sat G I α φ v → sat G I β φ v := by
  induction φ generalizing α β with
  | top => intro v _; trivial
  | bot => intro v h; exact h
  | atom pos e => intro v h; exact h
  | ref s => exact hc.elim
  | and a b iha ihb => intro v h; exact ⟨iha α β hc.1 v h.1, ihb α β hc.2 v h.2⟩
  | or a b iha ihb =>
      intro v h
      cases h with
      | inl ha => exact Or.inl (iha α β hc.1 v ha)
      | inr hb => exact Or.inr (ihb α β hc.2 v hb)
  | geq n π φ ih =>
      intro v ⟨l, hnd, hlen, hall⟩
      exact ⟨l, hnd, hlen, fun u hu => ⟨(hall u hu).1, ih α β hc u (hall u hu).2⟩⟩
  | amn n π φ ih =>
      intro v h l hnd hall
      exact h l hnd (fun u hu => ⟨(hall u hu).1, fun hα => (hall u hu).2 (ih α β hc u hα)⟩)
  | neigh e => intro v h; exact TE.Matches.of_nameFree I α β h hc
  | nneigh e => intro v h hm; exact h (TE.Matches.of_nameFree I β.compl α.compl hm hc)

/-- For a closed shape the dual is ordinary negation, under any assignment.
    This is what licenses `sh:not` and `sh:maxCount` on lower-stratum shapes. -/
theorem sat_dual_closed (G : Graph N P) (I : E → N → Prop) (α : Asg S N) (φ : Shape P S E)
    (hc : φ.Closed) (v : N) : sat G I α φ.dual v ↔ ¬ sat G I α φ v := by
  rw [← sat_dual G I α φ v]
  have hd : φ.dual.Closed := by
    clear v
    induction φ with
    | top => trivial
    | bot => trivial
    | atom pos e => trivial
    | ref s => exact hc.elim
    | and a b iha ihb => exact ⟨iha hc.1, ihb hc.2⟩
    | or a b iha ihb => exact ⟨iha hc.1, ihb hc.2⟩
    | geq n π φ ih => cases n with
        | zero => trivial
        | succ n => exact ih hc
    | amn n π φ ih => exact ih hc
    | neigh e => exact hc
    | nneigh e => exact hc
  exact ⟨sat_closed G I α α.compl φ.dual hd v, sat_closed G I α.compl α φ.dual hd v⟩

/-- SHACL `∃≤n π.φ` for closed `φ`. -/
def Shape.leq (n : Nat) (π : Path P) (φ : Shape P S E) : Shape P S E := .amn n π φ.dual

theorem sat_leq (G : Graph N P) (I : E → N → Prop) (α : Asg S N) (n : Nat) (π : Path P)
    (φ : Shape P S E) (hc : φ.Closed) (v : N) :
    sat G I α (.leq n π φ) v ↔
      ∀ l : List N, l.Nodup → (∀ u ∈ l, Path.Rel G π v u ∧ sat G I α φ u) → l.length ≤ n := by
  simp only [Shape.leq, sat]
  constructor
  · intro h l hnd hall
    exact h l hnd (fun u hu => ⟨(hall u hu).1,
      fun hd => ((sat_dual_closed G I α φ hc u).1 hd) (hall u hu).2⟩)
  · intro h l hnd hall
    refine h l hnd (fun u hu => ⟨(hall u hu).1, ?_⟩)
    apply Classical.byContradiction
    intro hns
    exact (hall u hu).2 ((sat_dual_closed G I α φ hc u).2 hns)

/-! ## ShEx surface forms -/

def TE.opt (e : TE P S E) : TE P S E := .alt e .eps

def TE.rep (e : TE P S E) : Nat → TE P S E
  | 0 => .eps
  | n+1 => .seq e (TE.rep e n)

/-- `e{m,}`. -/
def TE.atLeast (e : TE P S E) (m : Nat) : TE P S E := .seq (TE.rep e m) (.star e)

/-- `e{m,m+k}`. -/
def TE.between (e : TE P S E) (m k : Nat) : TE P S E := .seq (TE.rep e m) (TE.rep e.opt k)

/-- An ordinary ShEx shape: `e`, then any arcs whose step is not in `Q`
    (normally the steps `e` mentions, plus every inverse step it does not). -/
def Shape.openShape (e : TE P S E) (Q : List (Step P)) : Shape P S E :=
  .neigh (.seq e (.star (.anyExcept Q)))

end ShapesCore
