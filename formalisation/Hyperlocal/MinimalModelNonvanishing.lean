/-
  Hyperlocal/MinimalModelNonvanishing.lean

  Quartic “quartet factor” nonvanishing at an off-seed:
  the first Taylor coefficient (derivative at the seed) is nonzero as soon as
  Re(ρ) ≠ 1/2 and Im(ρ) ≠ 0.

  This is the k=1 “simple quartet” nondegeneracy input needed by the future
  implementation of `xiJetQuotRecOp`.
-/

import Hyperlocal.MinimalModel
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace MinimalModel

open scoped Real

lemma quartet_derivative_at_seed_ne_zero_of_re_im
    (ρ : ℂ) (hRe : ρ.re ≠ (1/2 : ℝ)) (hIm : ρ.im ≠ 0) :
    (Polynomial.derivative (quartetPoly ρ)).eval ρ ≠ 0 := by
  -- Use the closed form from `MinimalModel.quartet_derivative_at_seed`.
  have h1 : ρ - star ρ ≠ 0 := by
    intro h0
    have himEq : (ρ - star ρ).im = 0 := by
      simpa using congrArg Complex.im h0
    -- `(ρ - conj ρ).im = 2*ρ.im`
    have : (2 : ℝ) * ρ.im = 0 := by
      simpa using himEq
    have : ρ.im = 0 := by
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    exact hIm this

  have h2 : ρ - Hyperlocal.oneMinus ρ ≠ 0 := by
    intro h0
    have himEq : (ρ - Hyperlocal.oneMinus ρ).im = 0 := by
      simpa using congrArg Complex.im h0
    -- `(ρ - (1-ρ)).im = 2*ρ.im`
    have : (2 : ℝ) * ρ.im = 0 := by
      simpa [Hyperlocal.oneMinus] using himEq
    have : ρ.im = 0 := by
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    exact hIm this

  have h3 : ρ - Hyperlocal.oneMinus (star ρ) ≠ 0 := by
    intro h0
    -- take real parts
    have hreEq : ρ.re - (1 - ρ.re) = 0 := by
      -- (star ρ).re = ρ.re, and oneMinus is `1 - _`
      simpa [Hyperlocal.oneMinus] using congrArg Complex.re h0
    -- convert to 2*ρ.re - 1 = 0
    have hre : (2 : ℝ) * ρ.re - 1 = 0 := by
      linarith [hreEq]
    have : ρ.re = (1/2 : ℝ) := by
      linarith [hre]
    exact hRe this

  have h12 : (ρ - star ρ) * (ρ - Hyperlocal.oneMinus ρ) ≠ 0 :=
    mul_ne_zero h1 h2
  have hprod :
      (ρ - star ρ) * (ρ - Hyperlocal.oneMinus ρ) *
        (ρ - Hyperlocal.oneMinus (star ρ)) ≠ 0 :=
    mul_ne_zero h12 h3

  simpa [quartet_derivative_at_seed (ρ := ρ)] using hprod

end MinimalModel
end Hyperlocal
