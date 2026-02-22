/-
  Hyperlocal/Targets/XiPacket/TACJetQuotientRing_J3.lean

  Quotient-ring semantics for TAC transport at N=3:

    J3 := ℂ[w] / (w^3)
-/

import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex

/-- The ideal `(X^3)` inside `Polynomial ℂ`. -/
def J3Ideal : Ideal (Polynomial ℂ) :=
  Ideal.span ({(Polynomial.X : Polynomial ℂ) ^ 3} : Set (Polynomial ℂ))

/-- The cubic nilpotent quotient ring `ℂ[w]/(w^3)`. -/
abbrev J3 : Type := (Polynomial ℂ) ⧸ J3Ideal

namespace J3

/-- The canonical class of `X` in the quotient (the nilpotent `w`). -/
def w : J3 := Ideal.Quotient.mk _ Polynomial.X

@[simp] lemma w_def : (w : J3) = Ideal.Quotient.mk _ Polynomial.X := rfl

/-- In `J3`, `w^3 = 0`.  (Not a simp lemma: avoids simp recursion.) -/
lemma w_pow_three : (w : J3) ^ 3 = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
  change (Polynomial.X : Polynomial ℂ) ^ 3 ∈ J3Ideal
  dsimp [J3Ideal]
  exact Ideal.subset_span (by
    exact Set.mem_singleton _)

/-- Powers `w^n` vanish for `n ≥ 3`. -/
lemma w_pow_eq_zero_of_ge_three {n : ℕ} (hn : 3 ≤ n) : (w : J3) ^ n = 0 := by
  have hn' : n = 3 + (n - 3) := (Nat.add_sub_of_le hn).symm
  calc
    (w : J3) ^ n
        = (w : J3) ^ (3 + (n - 3)) := by
            -- no simp: just transport equality of exponents
            exact congrArg (fun m => (w : J3) ^ m) hn'
    _   = (w : J3) ^ 3 * (w : J3) ^ (n - 3) := by
            -- exact lemma, no simp
            exact pow_add (w : J3) 3 (n - 3)
    _   = 0 := by
            -- no simp: rewrite once and finish by `zero_mul`
            rw [w_pow_three]
            exact zero_mul _

end J3

end TAC
end XiPacket
end Targets
end Hyperlocal
