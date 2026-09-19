/-
One stratum of a shape catalogue, in negation normal form.

Type parameters:
  `P`  predicates
  `S`  shape names declared in THIS stratum; they occur only positively
  `E`  external atoms: anything whose extension is already fixed when this
       stratum is evaluated. Node tests `test(c)`, value types `test(τ)`,
       SHACL `closed(Q)`, `eq(π,p)`, `disj(π,p)`, and the shape names of
       lower strata are all atoms. Atoms may be negated.

This is the stratified discipline of KR 2026 Definition 3, built into the
syntax, so that every catalogue written in it has a monotone operator.
-/
import ShapesCore.Graph

namespace ShapesCore

/-- What a ShEx triple constraint may demand of the node at the far end. -/
inductive Target (S E : Type) where
  | name (s : S)
  | atom (pos : Bool) (e : E)

/-- ShEx triple expressions (KR 2026 Definition 6), shallow in the sense of
    its Proposition 2: a triple constraint points at a `Target`, not at a
    nested shape. `anyExcept Q` is one arc whose step is not in `Q`; the open
    and half-open forms are `seq e (star (anyExcept Q))`. -/
inductive TE (P S E : Type) where
  | eps
  | tc (st : Step P) (t : Target S E)
  | anyExcept (Q : List (Step P))
  | seq (a b : TE P S E)
  | alt (a b : TE P S E)
  | star (a : TE P S E)

/-- Shapes. `geq n π φ` is SHACL's `∃≥n π.φ`. `amn n π φ` ("at most n not")
    says at most `n` nodes reached by `π` FAIL `φ`; it is the monotone form of
    `∃≤n π.¬φ` and the dual of `geq (n+1)`. `neigh e` is the ShEx shape `{e}`;
    `nneigh e` is its dual. -/
inductive Shape (P S E : Type) where
  | top
  | bot
  | atom (pos : Bool) (e : E)
  | ref (s : S)
  | and (a b : Shape P S E)
  | or (a b : Shape P S E)
  | geq (n : Nat) (π : Path P) (φ : Shape P S E)
  | amn (n : Nat) (π : Path P) (φ : Shape P S E)
  | neigh (e : TE P S E)
  | nneigh (e : TE P S E)

/-- The dual shape (KR 2026, before Proposition 1): swap ⊤/⊥, ∧/∨, the two
    quantifier forms and the two neighbourhood forms, flip atoms, and leave
    same-stratum names alone. -/
def Shape.dual {P S E : Type} : Shape P S E → Shape P S E
  | .top => .bot
  | .bot => .top
  | .atom pos e => .atom (!pos) e
  | .ref s => .ref s
  | .and a b => .or a.dual b.dual
  | .or a b => .and a.dual b.dual
  | .geq 0 _ _ => .bot
  | .geq (n+1) π φ => .amn n π φ.dual
  | .amn n π φ => .geq (n+1) π φ.dual
  | .neigh e => .nneigh e
  | .nneigh e => .neigh e

/-- A catalogue for one stratum: a shape for every name. -/
abbrev Catalogue (P S E : Type) := S → Shape P S E

def Catalogue.dual {P S E : Type} (C : Catalogue P S E) : Catalogue P S E :=
  fun s => (C s).dual

end ShapesCore
