/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_EvalGermCoeff012.lean

  Step 2a (algebraic, cycle-safe):

  Rewrite the Step-1 coefficient `coeff a δ N k` for k = 0,1,2 into classical
  forms featuring the explicit factors:
    k=0 : 1
    k=1 : n
    k=2 : n*(n-1)/2
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_EvalGerm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC
namespace J3

open Complex
open scoped BigOperators

/-- k=0: `choose n 0 = 1`, `n-0 = n`. -/
lemma coeff_eq_sum_pow (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) :
    coeff a δ N 0 = (Finset.range N).sum (fun n => a n * δ ^ n) := by
  classical
  -- unfold and simp only the Nat-choose/power arithmetic for k=0
  simp [coeff, Nat.choose_zero_right]

/-- k=1: `choose n 1 = n`. (The `n=0` term is automatically 0.) -/
lemma coeff_eq_sum_mul_nat_pow_pred (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) :
    coeff a δ N 1 = (Finset.range N).sum (fun n => a n * (n : ℂ) * δ ^ (n - 1)) := by
  classical
  -- unfold and rewrite choose n 1
  simp [coeff, Nat.choose_one_right, mul_assoc, mul_left_comm, mul_comm]

/--
k=2: `choose n 2 = n*(n-1)/2`.

We keep it in the clean Nat-cast form:
  (Nat.choose n 2 : ℂ) = ((n*(n-1))/2 : ℕ) cast to ℂ.
That is usually *exactly* what you want to match to Toeplitz/transport entries.
-/
lemma coeff_eq_sum_choose_two (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) :
    coeff a δ N 2 =
      (Finset.range N).sum (fun n => a n * ((n * (n - 1) / 2 : ℕ) : ℂ) * δ ^ (n - 2)) := by
  classical
  -- `Nat.choose_two_right` is the key lemma: choose n 2 = n*(n-1)/2
  simp [coeff, Nat.choose_two_right, mul_assoc, mul_left_comm, mul_comm]

end J3
end TAC
end XiPacket
end Targets
end Hyperlocal
