/-
  Hyperlocal/Targets/XiPacket/TACMinimalModel_QuartetDerivNeZero.lean

  Structural lemma for Front NF:
  For an off-seed `s : OffSeed Xi`, the quartet factor `Rρk s.ρ 1`
  has a *simple* root at `s.ρ`, i.e.
      (Polynomial.derivative (Rρk s.ρ 1)).eval s.ρ ≠ 0.

  This is the key algebraic input needed later to translate
  "G is flat up to order 2 at ρ" into "Xi is flat up to order 3 at ρ"
  via the product rule for derivatives of (R * G).
-/

import Hyperlocal.Factorization
import Hyperlocal.MinimalModel
import Hyperlocal.AdAbsurdumSetup  -- OffSeed
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Polynomial

namespace TAC

/-- For `k = 1`, the quartet power model is definitionally the simple quartic. -/
lemma quartetPolyPow_one_eq (ρ : ℂ) :
    Hyperlocal.MinimalModel.quartetPolyPow ρ 1 = Hyperlocal.MinimalModel.quartetPoly ρ := by
  simp [Hyperlocal.MinimalModel.quartetPolyPow,
        Hyperlocal.MinimalModel.quartetPoly,
        Hyperlocal.MinimalModel.linPow,
        pow_one]

/--
**Simple root at the seed** for the k=1 quartet factor:

`(derivative (Rρk ρ 1)).eval ρ` is a product of three nonzero factors
whenever `ρ` is off the critical line and off the real axis.
-/
theorem Rρk_one_deriv_eval_seed_ne_zero (s : Hyperlocal.OffSeed Xi) :
    (Polynomial.derivative (Hyperlocal.Factorization.Rρk s.ρ 1)).eval s.ρ ≠ 0 := by
  have hR :
      Hyperlocal.Factorization.Rρk s.ρ 1 = Hyperlocal.MinimalModel.quartetPoly s.ρ := by
    simpa [Hyperlocal.Factorization.Rρk, quartetPolyPow_one_eq (ρ := s.ρ)]

  have hform :
      (Polynomial.derivative (Hyperlocal.Factorization.Rρk s.ρ 1)).eval s.ρ
        =
      (s.ρ - star s.ρ) * (s.ρ - Hyperlocal.oneMinus s.ρ) *
        (s.ρ - Hyperlocal.oneMinus (star s.ρ)) := by
    simpa [hR] using (Hyperlocal.MinimalModel.quartet_derivative_at_seed (ρ := s.ρ))

  have h1 : s.ρ - star s.ρ ≠ 0 := by
    intro h
    have hEq : s.ρ = star s.ρ := by
      exact sub_eq_zero.mp h

    -- Take imaginary parts: im ρ = im (star ρ) = -im ρ
    have him_neg : s.ρ.im = -s.ρ.im := by
      simpa using congrArg Complex.im hEq

    -- Convert x = -x into x = 0.
    have him0 : s.ρ.im = 0 := by
      -- linarith handles `x = -x` over ℝ.
      linarith

    -- OffSeed provides `ht : ρ.im ≠ 0` (or equivalent), so contradiction.
    exact s.ht (by simpa [him0])

  have h2 : s.ρ - Hyperlocal.oneMinus s.ρ ≠ 0 := by
    intro h
    have : s.ρ = Hyperlocal.oneMinus s.ρ := by
      exact sub_eq_zero.mp h
    have hre : s.ρ.re = (1 : ℝ) / 2 := by
      have := congrArg Complex.re this
      have : s.ρ.re = (1 : ℝ) - s.ρ.re := by
        simpa [Hyperlocal.oneMinus, sub_eq_add_neg] using this
      linarith
    exact s.hσ hre

  have h3 : s.ρ - Hyperlocal.oneMinus (star s.ρ) ≠ 0 := by
    intro h
    have : s.ρ = Hyperlocal.oneMinus (star s.ρ) := by
      exact sub_eq_zero.mp h
    have hre : s.ρ.re = (1 : ℝ) / 2 := by
      have := congrArg Complex.re this
      have : s.ρ.re = (1 : ℝ) - (star s.ρ).re := by
        simpa [Hyperlocal.oneMinus, sub_eq_add_neg] using this
      -- `(star ρ).re = ρ.re`
      have : s.ρ.re = (1 : ℝ) - s.ρ.re := by
        simpa using this
      linarith
    exact s.hσ hre

  have hprod :
      (s.ρ - star s.ρ) * (s.ρ - Hyperlocal.oneMinus s.ρ) *
        (s.ρ - Hyperlocal.oneMinus (star s.ρ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero h1 h2) h3

  simpa [hform] using hprod

end TAC

end XiPacket
end Targets
end Hyperlocal
