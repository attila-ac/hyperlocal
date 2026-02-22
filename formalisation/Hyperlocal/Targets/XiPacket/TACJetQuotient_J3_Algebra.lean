/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_Algebra.lean

  Pure algebra in J3 := ℂ[w]/(w^3):

  * embed ℂ →+* J3
  * define u := δ + w  (NOT nilpotent in general)
  * prove finite-range truncation for sums with w^n (tail vanishes for n≥3)
  * define the order-2 jet polynomial in J3
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotientRing_J3
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open scoped BigOperators
open Complex

namespace J3

/-- The canonical ring hom `ℂ →+* J3` (constants into the quotient). -/
def C : ℂ →+* J3 :=
  (Ideal.Quotient.mk _).comp Polynomial.C

@[simp] lemma C_apply (c : ℂ) :
    C c = (Ideal.Quotient.mk _ (Polynomial.C c) : J3) := rfl

/-- The shift element `u = δ + w` in the quotient (not nilpotent in general). -/
def u (δ : ℂ) : J3 := C δ + (w : J3)

/--
If you evaluate any sequence `(a n)` against powers of `w`, the sum over `range N`
stabilizes at 3: terms with `n ≥ 3` are zero.
-/
lemma sum_range_eq_sum_range_three_of_w_nil
    (a : ℕ → J3) (N : ℕ) (hN : 3 ≤ N) :
    (Finset.range N).sum (fun n => a n * (w : J3) ^ n)
      =
    (Finset.range 3).sum (fun n => a n * (w : J3) ^ n) := by
  classical

  -- Split `range N` as `range 3` plus a tail.
  have hdecomp : 3 + (N - 3) = N := by
    exact Nat.add_sub_of_le hN

  have hsplit :
      (Finset.range N).sum (fun n => a n * (w : J3) ^ n)
        =
      (Finset.range 3).sum (fun n => a n * (w : J3) ^ n)
        +
      (Finset.range (N - 3)).sum (fun t => a (3 + t) * (w : J3) ^ (3 + t)) := by
    simpa [hdecomp] using
      (Finset.sum_range_add (fun n => a n * (w : J3) ^ n) 3 (N - 3))

  -- Tail sum is zero because `w^(3+t)=0`.
  have htail :
      (Finset.range (N - 3)).sum (fun t => a (3 + t) * (w : J3) ^ (3 + t)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have ht' : 3 ≤ 3 + t := by
      exact Nat.le_add_right 3 t
    have hw : (w : J3) ^ (3 + t) = 0 := by
      exact w_pow_eq_zero_of_ge_three (n := 3 + t) ht'
    -- no simp, no mk-normalization: just rewrite by `hw`.
    rw [hw]
    exact mul_zero _

  -- Finish: rewrite the split and kill the tail.
  calc
    (Finset.range N).sum (fun n => a n * (w : J3) ^ n)
        =
      (Finset.range 3).sum (fun n => a n * (w : J3) ^ n)
        +
      (Finset.range (N - 3)).sum (fun t => a (3 + t) * (w : J3) ^ (3 + t)) := hsplit
    _ =
      (Finset.range 3).sum (fun n => a n * (w : J3) ^ n) := by
      rw [htail]
      simp

/--
Order-2 jet polynomial (in `w`) with coefficients in ℂ, viewed inside J3:
`a0 + a1*w + a2*w^2`.
-/
def jet2 (a0 a1 a2 : ℂ) : J3 :=
  C a0 + (C a1) * (w : J3) + (C a2) * (w : J3) ^ 2

@[simp] lemma jet2_def (a0 a1 a2 : ℂ) :
    jet2 a0 a1 a2 = C a0 + (C a1) * (w : J3) + (C a2) * (w : J3) ^ 2 := rfl

end J3

end TAC
end XiPacket
end Targets
end Hyperlocal
