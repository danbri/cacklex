/-
The reachability tests of KR 2026 section 3, run and then turned into theorems
about the declarative semantics through `checkLfp_correct` / `checkGfp_correct`.

Graph: b → a, and c ⇄ d, all by predicate p.
Catalogue: r : test(a) ∨ ∃p.r   ("can reach a").
Paper: LFP = {a, b};  GFP = {a, b, c, d}.
-/
import ShapesCore.Schema

namespace ShapesCore.ExamplesExec
open ShapesCore

inductive Nd where
  | a | b | c | d
deriving DecidableEq, Repr

def G : Graph Nd Unit := ⟨[(.b, (), .a), (.c, (), .d), (.d, (), .c)]⟩
def nodes : List Nd := [.a, .b, .c, .d]

/-- The single atom: "is the node a". -/
def Ib : Unit → Nd → Bool := fun _ v => decide (v = .a)

def C : Catalogue Unit Unit Unit := fun _ => .or (.atom true ()) (.ex (.fwd ()) (.ref ()))

#eval solveLfp G Ib C [()] nodes          -- some [((), a), ((), b)]
#eval nodes.map (checkLfp G Ib C [()] nodes ())   -- [true, true, false, false]
#eval nodes.map (checkGfp G Ib C [()] nodes ())   -- [true, true, true, true]

theorem hx : ∀ s, (C s).Exec := fun _ => ⟨trivial, trivial⟩
theorem hnames : ∀ s : Unit, s ∈ [()] := fun s => by cases s; simp
theorem hcl : G.ClosedIn nodes := by
  intro t ht
  simp [G] at ht
  rcases ht with rfl | rfl | rfl <;> simp [nodes]

/-- c cannot reach a: not in the least fixpoint. -/
theorem reach1_lfp_c : ¬ lfp G (fun e v => Ib e v = true) C () .c := by
  have h : checkLfp G Ib C [()] nodes () .c = some false := by decide
  have := checkLfp_correct G Ib C [()] nodes hx hnames hcl () .c (by simp [nodes]) false h
  simpa using this

/-- b can. -/
theorem reach1_lfp_b : lfp G (fun e v => Ib e v = true) C () .b := by
  have h : checkLfp G Ib C [()] nodes () .b = some true := by decide
  exact (checkLfp_correct G Ib C [()] nodes hx hnames hcl () .b (by simp [nodes]) true h).1 rfl

/-- Under GFP the cycle c ⇄ d supports itself, so c is accepted. -/
theorem reach1_gfp_c : gfp G (fun e v => Ib e v = true) C () .c := by
  have h : checkGfp G Ib C [()] nodes () .c = some true := by decide
  exact (checkGfp_correct G Ib C [()] nodes hx hnames hcl () .c (by simp [nodes]) true h).1 rfl

/-- The paper's selector map for reach1: r must hold at all four nodes. -/
def sel : SelectorMap Unit Unit Unit := [((), .top)]

#eval conformsLfp G Ib C sel [()] nodes   -- some false: an engine using LFP rejects
#eval conformsGfp G Ib C sel [()] nodes   -- some true:  an engine using GFP accepts

/-- The same graph and schema conform under GFP and not under LFP. -/
theorem reach1_separates :
    ConformsOn G (fun e v => Ib e v = true) (gfp G (fun e v => Ib e v = true) C) sel nodes ∧
    ¬ ConformsOn G (fun e v => Ib e v = true) (lfp G (fun e v => Ib e v = true) C) sel nodes := by
  have hsel : ∀ p ∈ sel, p.2.Exec := by intro p hp; simp [sel] at hp; subst hp; trivial
  constructor
  · have h : conformsGfp G Ib C sel [()] nodes = some true := by decide
    exact (conformsGfp_correct G Ib C sel [()] nodes hx hsel hnames hcl true h).1 rfl
  · have h : conformsLfp G Ib C sel [()] nodes = some false := by decide
    have := conformsLfp_correct G Ib C sel [()] nodes hx hsel hnames hcl false h
    simpa using this

end ShapesCore.ExamplesExec
