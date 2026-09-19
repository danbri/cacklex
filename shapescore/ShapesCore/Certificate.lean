/-
Certificates: verify an answer without trusting, or re-running, the solver.

An untrusted engine (the F* build, rudof, shex.js, the JS draft) produces an
assignment. The verified side only applies the operator ONCE and compares.

  in LFP      a chain of stages, each derivable in one round from the last
  in GFP      one set that is post-fixed: every member re-derives from the set
  not in GFP  a chain for the DUAL catalogue      (Proposition 1)
  not in LFP  a post-fixed set for the DUAL catalogue

So a refutation is a proof in the dual catalogue, and every verdict has a
certificate of one of two shapes. None of the four theorems needs the node
list to be closed or the name list complete; only `Exec`. A ShEx result shape
map is already a certificate of the second kind.
-/
import ShapesCore.Schema

namespace ShapesCore

variable {N P S E : Type} [DecidableEq N] [DecidableEq P] [DecidableEq S]

/-- Every pair of `next` holds after one round from `prev`. -/
def derivesB (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E)
    (prev next : FAsg S N) : Bool :=
  next.all fun x => evalB G Ib prev (C x.1) x.2

def chainB (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E) :
    FAsg S N → List (FAsg S N) → Bool
  | _, [] => true
  | prev, next :: rest => derivesB G Ib C prev next && chainB G Ib C next rest

def postfixedB (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E) (a : FAsg S N) : Bool :=
  derivesB G Ib C a a

section
variable (G : Graph N P) (Ib : E → N → Bool) (C : Catalogue P S E) (hx : ∀ s, (C s).Exec)

local notation "I'" => (fun (e : E) (v : N) => Ib e v = true)

include hx in
theorem chain_sound : ∀ (stages : List (FAsg S N)) (prev : FAsg S N),
    prev.toAsg.le (lfp G I' C) → chainB G Ib C prev stages = true →
    ∀ a ∈ stages, a.toAsg.le (lfp G I' C) := by
  intro stages
  induction stages with
  | nil => intro _ _ _ a ha; cases ha
  | cons next rest ih =>
      intro prev hprev hc a ha
      simp only [chainB, Bool.and_eq_true] at hc
      have hnext : next.toAsg.le (lfp G I' C) := by
        intro s v hm
        have hb := List.all_eq_true.1 hc.1 (s, v) hm
        have hs := (evalB_iff G Ib prev (C s) (hx s) v).1 hb
        exact T_lfp_le G I' C s v (sat_mono G I' hprev (C s) v hs)
      cases List.mem_cons.1 ha with
      | inl e => subst e; exact hnext
      | inr m => exact ih next hnext hc.2 a m

include hx in
/-- A checked chain from the empty assignment proves LFP membership. -/
theorem lfp_of_chain (stages : List (FAsg S N)) (h : chainB G Ib C [] stages = true)
    (a : FAsg S N) (ha : a ∈ stages) (s : S) (v : N) (hm : (s, v) ∈ a) : lfp G I' C s v :=
  chain_sound G Ib C hx stages [] (fun s v hm => by simp [FAsg.toAsg] at hm) h a ha s v hm

include hx in
/-- A checked post-fixed set proves GFP membership. -/
theorem gfp_of_postfixed (a : FAsg S N) (h : postfixedB G Ib C a = true)
    (s : S) (v : N) (hm : (s, v) ∈ a) : gfp G I' C s v := by
  refine le_gfp_of_postfixed G I' C (α := a.toAsg) ?_ s v hm
  intro s' v' hm'
  exact (evalB_iff G Ib a (C s') (hx s') v').1 (List.all_eq_true.1 h (s', v') hm')

include hx in
/-- Refuting GFP membership: a chain for the dual catalogue. -/
theorem not_gfp_of_dual_chain (stages : List (FAsg S N))
    (h : chainB G Ib C.dual [] stages = true) (a : FAsg S N) (ha : a ∈ stages)
    (s : S) (v : N) (hm : (s, v) ∈ a) : ¬ gfp G I' C s v := by
  rw [gfp_iff_not_lfp_dual]
  exact fun hn => hn (lfp_of_chain G Ib C.dual (fun s => dual_exec (C s) (hx s)) stages h a ha s v hm)

include hx in
/-- Refuting LFP membership: a post-fixed set for the dual catalogue. -/
theorem not_lfp_of_dual_postfixed (a : FAsg S N) (h : postfixedB G Ib C.dual a = true)
    (s : S) (v : N) (hm : (s, v) ∈ a) : ¬ lfp G I' C s v := by
  rw [lfp_iff_not_gfp_dual]
  exact fun hn => hn (gfp_of_postfixed G Ib C.dual (fun s => dual_exec (C s) (hx s)) a h s v hm)

end
end ShapesCore
