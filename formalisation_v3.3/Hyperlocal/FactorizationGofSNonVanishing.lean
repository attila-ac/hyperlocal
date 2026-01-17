import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization

noncomputable section
open Polynomial Complex

namespace Hyperlocal
namespace FactorizationAnalytic

/-- Local evaluation: (X - z)^k at s is (s - z)^k. -/
@[simp] lemma eval_linPow_local (s z : ℂ) (k : ℕ) :
    (Hyperlocal.MinimalModel.linPow z k).eval s = (s - z) ^ k := by
  simp only [Hyperlocal.MinimalModel.linPow, Hyperlocal.MinimalModel.lin, eval_pow, eval_sub, eval_X, eval_C]

/-- The product of the other three quartet factors (each to power k). -/
def Qρk (ρ : ℂ) (k : ℕ) : Polynomial ℂ :=
  Hyperlocal.MinimalModel.linPow (star ρ) k
  * Hyperlocal.MinimalModel.linPow (Hyperlocal.oneMinus ρ) k
  * Hyperlocal.MinimalModel.linPow (Hyperlocal.oneMinus (star ρ)) k

/-- If the three "other" differences are nonzero at ρ, then their product (evaluated at ρ) is nonzero. -/
lemma Qρk_eval_ne_zero_of_separations {ρ : ℂ} {k : ℕ} (hk : k ≥ 1)
    (h1 : ρ ≠ star ρ)
    (h2 : ρ ≠ Hyperlocal.oneMinus ρ)
    (h3 : ρ ≠ Hyperlocal.oneMinus (star ρ)) :
    (Qρk ρ k).eval ρ ≠ 0 := by
  simp only [Qρk, eval_mul, eval_linPow_local]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero k (sub_ne_zero.mpr h1)
    · exact pow_ne_zero k (sub_ne_zero.mpr h2)
  · exact pow_ne_zero k (sub_ne_zero.mpr h3)

end FactorizationAnalytic
end Hyperlocal
