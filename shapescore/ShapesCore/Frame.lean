/-
Two families of theorems about how verdicts and inferences move when the
graph changes. Both are aimed at a store built from immutable,
predicate-partitioned blocks with an append-only delta log (Factoidal's
Shardborough specification, abstract).

FRAME. Fix the set `Rel` of steps a catalogue uses, and a region `R` of nodes
closed under those steps. If two graphs agree on the `Rel`-arcs leaving `R`,
every node of `R` has the same LFP and GFP verdicts in both (`lfp_frame`,
`gfp_frame`). Nothing is assumed about other predicates or about nodes outside
`R`. Consequences: validation needs only the blocks of the predicates the
schema mentions; a cached verdict survives any change outside its region; and
disjoint regions can be validated independently. This is the precise form of
the remark in the ShEx 2.0 specification that validation "does not necessarily
require" a shape map over every node, since the semantics induces a set of
dependencies.

APPEND. For shapes built without upper bounds (`Positive`), verdicts are
monotone in the graph: what held before an append holds after
(`lfp_append`). For shapes built without lower bounds (`Universal`), GFP
verdicts are antitone: a violation is never repaired by adding triples
(`gfp_shrink`). Forward-chained facts are monotone in the base graph
(`rules_append`), so earlier certificate stages stay valid across generations.
-/
import ShapesCore.Rules

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N]

/-! ## Frame -/

/-- The executable fragment, with every step drawn from `Rel`. -/
def Shape.ExecOn (Rel : Step P → Prop) : Shape P S E → Prop
  | .top => True
  | .bot => True
  | .atom _ _ => True
  | .ref _ => True
  | .and a b => a.ExecOn Rel ∧ b.ExecOn Rel
  | .or a b => a.ExecOn Rel ∧ b.ExecOn Rel
  | .geq _ (.step st) φ => Rel st ∧ φ.ExecOn Rel
  | .geq _ _ _ => False
  | .amn _ (.step st) φ => Rel st ∧ φ.ExecOn Rel
  | .amn _ _ _ => False
  | .neigh _ => False
  | .nneigh _ => False

theorem sat_frame (G G' : Graph N P) (I : E → N → Prop) (Rel : Step P → Prop) (R : N → Prop)
    (hcl : ∀ v, R v → ∀ st u, Rel st → G.arc v st u → R u)
    (hag : ∀ v, R v → ∀ st u, Rel st → (G.arc v st u ↔ G'.arc v st u))
    {α β : Asg S N} (h : ∀ s u, R u → α s u → β s u) (φ : Shape P S E) (hx : φ.ExecOn Rel) :
    ∀ v, R v → sat G I α φ v → sat G' I β φ v := by
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
          intro v hv ⟨l, hnd, hlen, hall⟩
          refine ⟨l, hnd, hlen, fun u hu => ?_⟩
          have harc := (Path.rel_step_iff G st v u).1 (hall u hu).1
          exact ⟨.step ((hag v hv st u hx.1).1 harc),
            ih hx.2 u (hcl v hv st u hx.1 harc) (hall u hu).2⟩
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | amn n π φ ih =>
      cases π with
      | step st =>
          intro v hv hs l hnd hall
          refine hs l hnd (fun u hu => ?_)
          have harc' := (Path.rel_step_iff G' st v u).1 (hall u hu).1
          have harc := (hag v hv st u hx.1).2 harc'
          exact ⟨.step harc, fun hα =>
            (hall u hu).2 (ih hx.2 u (hcl v hv st u hx.1 harc) hα)⟩
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

theorem lfp_frame_le (G G' : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    (Rel : Step P → Prop) (R : N → Prop)
    (hcl : ∀ v, R v → ∀ st u, Rel st → G.arc v st u → R u)
    (hag : ∀ v, R v → ∀ st u, Rel st → (G.arc v st u ↔ G'.arc v st u))
    (hx : ∀ s, (C s).ExecOn Rel) : ∀ s v, R v → lfp G I C s v → lfp G' I C s v := by
  intro s v hv hl
  have hpre : (T G I C (fun s v => ¬ R v ∨ lfp G' I C s v)).le
      (fun s v => ¬ R v ∨ lfp G' I C s v) := by
    intro s' v' hT
    cases Classical.em (R v') with
    | inr hn => exact Or.inl hn
    | inl hr =>
        refine Or.inr (T_lfp_le G' I C s' v' ?_)
        exact sat_frame G G' I Rel R hcl hag
          (fun s u hu h' => h'.elim (fun hn => absurd hu hn) id) (C s') (hx s') v' hr hT
  cases hl _ hpre with
  | inl hn => exact absurd hv hn
  | inr h' => exact h'

/-- Frame theorem, LFP. -/
theorem lfp_frame (G G' : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    (Rel : Step P → Prop) (R : N → Prop)
    (hcl : ∀ v, R v → ∀ st u, Rel st → G.arc v st u → R u)
    (hag : ∀ v, R v → ∀ st u, Rel st → (G.arc v st u ↔ G'.arc v st u))
    (hx : ∀ s, (C s).ExecOn Rel) (s : S) (v : N) (hv : R v) :
    lfp G I C s v ↔ lfp G' I C s v :=
  ⟨lfp_frame_le G G' I C Rel R hcl hag hx s v hv,
   lfp_frame_le G' G I C Rel R
     (fun v hv st u hr ha => hcl v hv st u hr ((hag v hv st u hr).2 ha))
     (fun v hv st u hr => (hag v hv st u hr).symm) hx s v hv⟩

omit [DecidableEq N] in
theorem dual_execOn (Rel : Step P → Prop) (φ : Shape P S E) (hx : φ.ExecOn Rel) :
    φ.dual.ExecOn Rel := by
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
        | succ n => exact ⟨hx.1, ih hx.2⟩
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | amn n π φ ih =>
      cases π with
      | step st => exact ⟨hx.1, ih hx.2⟩
      | id => exact hx.elim
      | seq _ _ => exact hx.elim
      | alt _ _ => exact hx.elim
      | star _ => exact hx.elim
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

/-- Frame theorem, GFP (the ShEx reading), through duality. -/
theorem gfp_frame (G G' : Graph N P) (I : E → N → Prop) (C : Catalogue P S E)
    (Rel : Step P → Prop) (R : N → Prop)
    (hcl : ∀ v, R v → ∀ st u, Rel st → G.arc v st u → R u)
    (hag : ∀ v, R v → ∀ st u, Rel st → (G.arc v st u ↔ G'.arc v st u))
    (hx : ∀ s, (C s).ExecOn Rel) (s : S) (v : N) (hv : R v) :
    gfp G I C s v ↔ gfp G' I C s v := by
  rw [gfp_iff_not_lfp_dual, gfp_iff_not_lfp_dual]
  exact not_congr (lfp_frame G G' I C.dual Rel R hcl hag
    (fun s => dual_execOn Rel (C s) (hx s)) s v hv)

/-! ## Append -/

def Graph.le (G G' : Graph N P) : Prop := ∀ t, t ∈ G.triples → t ∈ G'.triples

omit [DecidableEq N] in
theorem Graph.arc_mono {G G' : Graph N P} (h : G.le G') {v u : N} {st : Step P} :
    G.arc v st u → G'.arc v st u := by
  cases st <;> intro ha <;> exact h _ ha

omit [DecidableEq N] in
theorem Path.Rel.mono {G G' : Graph N P} (h : G.le G') {π : Path P} {v u : N}
    (r : Path.Rel G π v u) : Path.Rel G' π v u := by
  induction r with
  | id v => exact .id v
  | step ha => exact .step (Graph.arc_mono h ha)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | altL _ ih => exact .altL ih
  | altR _ ih => exact .altR ih
  | starNil v => exact .starNil v
  | starCons _ _ ih1 ih2 => exact .starCons ih1 ih2

/-- No upper bounds and no closedness: lower bounds over any path. -/
def Shape.Positive : Shape P S E → Prop
  | .top => True
  | .bot => True
  | .atom _ _ => True
  | .ref _ => True
  | .and a b => a.Positive ∧ b.Positive
  | .or a b => a.Positive ∧ b.Positive
  | .geq _ _ φ => φ.Positive
  | .amn _ _ _ => False
  | .neigh _ => False
  | .nneigh _ => False

/-- No lower bounds: "at most n fail" over any path. -/
def Shape.Universal : Shape P S E → Prop
  | .top => True
  | .bot => True
  | .atom _ _ => True
  | .ref _ => True
  | .and a b => a.Universal ∧ b.Universal
  | .or a b => a.Universal ∧ b.Universal
  | .geq _ _ _ => False
  | .amn _ _ φ => φ.Universal
  | .neigh _ => False
  | .nneigh _ => False

theorem sat_append {G G' : Graph N P} (hle : G.le G') (I : E → N → Prop) (α : Asg S N)
    (φ : Shape P S E) (hx : φ.Positive) : ∀ v, sat G I α φ v → sat G' I α φ v := by
  induction φ with
  | top => intro v _; trivial
  | bot => intro v hf; exact hf
  | atom pos e => intro v hs; exact hs
  | ref s => intro v hs; exact hs
  | and x y ihx ihy => intro v hs; exact ⟨ihx hx.1 v hs.1, ihy hx.2 v hs.2⟩
  | or x y ihx ihy =>
      intro v hs
      cases hs with
      | inl ha => exact Or.inl (ihx hx.1 v ha)
      | inr hb => exact Or.inr (ihy hx.2 v hb)
  | geq n π φ ih =>
      intro v ⟨l, hnd, hlen, hall⟩
      exact ⟨l, hnd, hlen, fun u hu => ⟨Path.Rel.mono hle (hall u hu).1, ih hx u (hall u hu).2⟩⟩
  | amn n π φ ih => exact hx.elim
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

theorem sat_shrink {G G' : Graph N P} (hle : G.le G') (I : E → N → Prop) (α : Asg S N)
    (φ : Shape P S E) (hx : φ.Universal) : ∀ v, sat G' I α φ v → sat G I α φ v := by
  induction φ with
  | top => intro v _; trivial
  | bot => intro v hf; exact hf
  | atom pos e => intro v hs; exact hs
  | ref s => intro v hs; exact hs
  | and x y ihx ihy => intro v hs; exact ⟨ihx hx.1 v hs.1, ihy hx.2 v hs.2⟩
  | or x y ihx ihy =>
      intro v hs
      cases hs with
      | inl ha => exact Or.inl (ihx hx.1 v ha)
      | inr hb => exact Or.inr (ihy hx.2 v hb)
  | geq n π φ ih => exact hx.elim
  | amn n π φ ih =>
      intro v hs l hnd hall
      exact hs l hnd (fun u hu =>
        ⟨Path.Rel.mono hle (hall u hu).1, fun h' => (hall u hu).2 (ih hx u h')⟩)
  | neigh e => exact hx.elim
  | nneigh e => exact hx.elim

/-- Appends preserve every LFP verdict of a positive catalogue. -/
theorem lfp_append {G G' : Graph N P} (hle : G.le G') (I : E → N → Prop) (C : Catalogue P S E)
    (hpos : ∀ s, (C s).Positive) : (lfp G I C).le (lfp G' I C) :=
  lfp_le_of_prefixed G I C (fun s v hT =>
    T_lfp_le G' I C s v (sat_append hle I _ (C s) (hpos s) v hT))

/-- Appends never repair a GFP violation of a universal catalogue. -/
theorem gfp_shrink {G G' : Graph N P} (hle : G.le G') (I : E → N → Prop) (C : Catalogue P S E)
    (huni : ∀ s, (C s).Universal) : (gfp G' I C).le (gfp G I C) :=
  le_gfp_of_postfixed G I C (fun s v hg =>
    sat_shrink hle I _ (C s) (huni s) v (gfp_le_T G' I C s v hg))

/-- Forward-chained facts are monotone in the base graph. -/
theorem rules_append {N P : Type} [DecidableEq N] [DecidableEq P] (G G' : List (Tr N P))
    (K : RuleKernel N P) (U : List (Tr N P)) (h : ∀ t, t ∈ G → t ∈ G') :
    ∀ f, (rulesOp G K U).lfp f → (rulesOp G' K U).lfp f := by
  intro f hl
  refine hl (rulesOp G' K U).lfp ?_
  intro g hT
  refine (rulesOp G' K U).T_lfp_le g ⟨hT.1, ?_⟩
  rcases hT.2 with (hg | hs) | hj
  · exact Or.inl (Or.inl (h g hg))
  · exact Or.inl (Or.inr hs)
  · exact Or.inr hj

end ShapesCore
