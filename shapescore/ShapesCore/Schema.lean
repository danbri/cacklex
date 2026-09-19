/-
Schemas: a catalogue plus a selector map (KR 2026 section 2.4). A selector
abstracts SHACL targets and ShEx shape maps: a shape that mentions no names,
paired with the name every selected node must have.

Selected nodes are drawn from the listed nodes. The paper also allows a
selector to pick a constant that is not in the graph (its `fresh` test); to
cover that, list the constant among the nodes.
-/
import ShapesCore.Iterate

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N] [DecidableEq P] [DecidableEq S]

abbrev SelectorMap (P S E : Type) := List (S × Shape P S E)

/-- `G` conforms under the assignment `X` (LFP or GFP of the catalogue):
    every listed node matching a selector has the selector's shape name. -/
def ConformsOn (G : Graph N P) (I : E → N → Prop) (X : Asg S N) (sel : SelectorMap P S E)
    (nodes : List N) : Prop :=
  ∀ p ∈ sel, ∀ v ∈ nodes, sat G I (FAsg.toAsg ([] : FAsg S N)) p.2 v → X p.1 v

def conformsWith (G : Graph N P) (Ib : E → N → Bool) (sel : SelectorMap P S E) (nodes : List N)
    (holds : S → N → Bool) : Bool :=
  sel.all fun p => nodes.all fun v => !(evalB G Ib ([] : FAsg S N) p.2 v) || holds p.1 v

def conformsLfp (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E) (sel : SelectorMap P S E)
    (names : List S) (nodes : List N) : Option Bool :=
  (solveLfp G Ib C names nodes).map fun a => conformsWith G Ib sel nodes (fun s v => decide ((s, v) ∈ a))

def conformsGfp (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E) (sel : SelectorMap P S E)
    (names : List S) (nodes : List N) : Option Bool :=
  (solveLfp G Ib C.dual names nodes).map fun a => conformsWith G Ib sel nodes (fun s v => !decide ((s, v) ∈ a))

theorem conformsWith_iff (G : Graph N P) (Ib : E → N → Bool) (sel : SelectorMap P S E)
    (nodes : List N) (hsel : ∀ p ∈ sel, p.2.Exec) (holds : S → N → Bool) (X : Asg S N)
    (hX : ∀ s v, v ∈ nodes → (holds s v = true ↔ X s v)) :
    conformsWith G Ib sel nodes holds = true ↔
      ConformsOn G (fun e v => Ib e v = true) X sel nodes := by
  simp only [conformsWith, List.all_eq_true, ConformsOn]
  constructor
  · intro h p hp v hv hs
    have hb := (evalB_iff G Ib [] p.2 (hsel p hp) v).2 hs
    have := h p hp v hv
    simp [hb] at this
    exact (hX p.1 v hv).1 this
  · intro h p hp v hv
    cases hb : evalB G Ib ([] : FAsg S N) p.2 v with
    | false => simp
    | true =>
        have := h p hp v hv ((evalB_iff G Ib [] p.2 (hsel p hp) v).1 hb)
        simp [(hX p.1 v hv).2 this]

theorem conformsLfp_correct (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (sel : SelectorMap P S E) (names : List S) (nodes : List N)
    (hx : ∀ s, (C s).Exec) (hsel : ∀ p ∈ sel, p.2.Exec) (hnames : ∀ s, s ∈ names)
    (hcl : G.ClosedIn nodes) (b : Bool) (h : conformsLfp G Ib C sel names nodes = some b) :
    b = true ↔ ConformsOn G (fun e v => Ib e v = true) (lfp G (fun e v => Ib e v = true) C) sel nodes := by
  simp only [conformsLfp, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  refine conformsWith_iff G Ib sel nodes hsel _ _ (fun s v hv => ?_)
  rw [decide_eq_true_eq]
  exact solveLfp_correct G Ib C names nodes hx hnames hcl a ha s v hv

theorem conformsGfp_correct (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (sel : SelectorMap P S E) (names : List S) (nodes : List N)
    (hx : ∀ s, (C s).Exec) (hsel : ∀ p ∈ sel, p.2.Exec) (hnames : ∀ s, s ∈ names)
    (hcl : G.ClosedIn nodes) (b : Bool) (h : conformsGfp G Ib C sel names nodes = some b) :
    b = true ↔ ConformsOn G (fun e v => Ib e v = true) (gfp G (fun e v => Ib e v = true) C) sel nodes := by
  simp only [conformsGfp, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  refine conformsWith_iff G Ib sel nodes hsel _ _ (fun s v hv => ?_)
  rw [gfp_iff_not_lfp_dual]
  have := solveLfp_correct G Ib C.dual names nodes (fun s => dual_exec (C s) (hx s)) hnames hcl a ha s v hv
  simp [← this]

end ShapesCore
