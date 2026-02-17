/-
  Hyperlocal/Targets/XiTransportConvolution.lean

  Green, heartbeat-stable version.

  Purpose:
  Provide small, local lemmas bridging the concrete transport operator
  (Toeplitz-right with shift-stencil) to explicit finite Cauchy coefficients
  against a zero-padded window sequence.

  Key design choices (to avoid recursion/heartbeats):
  * Do NOT introduce general “sum = convCoeff” rewrites (those tend to trigger whnf/isDefEq loops).
  * Do NOT use nested `simpa`/`simp` on large goals.
  * Instead: prove explicit closed forms for the specific RHS sums that appear in the three
    `Fin` cases (range 1/2/3) by direct `simp` on those sums, with `winSeqStd` rfl-lemmas.

  Status:
  This file should compile; remaining warnings are only linter-level (if any).
-/

import Hyperlocal.Targets.XiTransportOp
import Hyperlocal.Cancellation.Recurrence
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
-- If your project uses very tight heartbeats, you may want:
-- set_option maxHeartbeats 400000
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiTransport

open scoped BigOperators
open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Standard zero-padded sequence view of a `Window 3`. -/
def winSeqStd (w : Window 3) : ℕ → ℂ
  | 0 => w 0
  | 1 => w 1
  | 2 => w 2
  | _ => 0

@[simp] lemma winSeqStd0 (w : Window 3) : winSeqStd w 0 = w 0 := rfl
@[simp] lemma winSeqStd1 (w : Window 3) : winSeqStd w 1 = w 1 := rfl
@[simp] lemma winSeqStd2 (w : Window 3) : winSeqStd w 2 = w 2 := rfl

/-!
  ### `shiftR'` simp lemmas on `Window 3` for `n = 2`
-/

@[simp] lemma shiftR'_one (w : Window 3) : shiftR' (n := 2) w 1 = w 0 := by
  simpa using (shiftR'_succ (n := 2) w (0 : Fin 2))

@[simp] lemma shiftR'_two (w : Window 3) : shiftR' (n := 2) w 2 = w 1 := by
  simpa using (shiftR'_succ (n := 2) w (1 : Fin 2))

@[simp] lemma shiftR'_shiftR'_one (w : Window 3) :
    shiftR' (n := 2) (shiftR' (n := 2) w) 1 = 0 := by
  -- (shiftR'(shiftR' w)) 1 = (shiftR' w) 0, and shiftR' at 0 is 0
  simpa using (shiftR'_succ (n := 2) (shiftR' (n := 2) w) (0 : Fin 2))

@[simp] lemma shiftR'_shiftR'_two (w : Window 3) :
    shiftR' (n := 2) (shiftR' (n := 2) w) 2 = w 0 := by
  -- (shiftR'(shiftR' w)) 2 = (shiftR' w) 1 = w 0
  have h := shiftR'_succ (n := 2) (shiftR' (n := 2) w) (1 : Fin 2)
  -- RHS is (shiftR' w) 1; rewrite that to w 0
  simpa [shiftR'_one] using h

/-!
  ### Closed-form `convCoeff` against `winSeqStd` at indices 0,1,2.
  (Kept because they are useful in later bridge files, but we do NOT rely on
   converting RHS “range-sums” to `convCoeff` via definitional unfolding in the main lemma.)
-/

@[simp] lemma convCoeff_winSeqStd_zero (a : ℕ → ℂ) (w : Window 3) :
    convCoeff a (winSeqStd w) 0 = a 0 * w 0 := by
  classical
  simp [Hyperlocal.Cancellation.convCoeff, Hyperlocal.Cancellation.coeff, winSeqStd]

@[simp] lemma convCoeff_winSeqStd_one (a : ℕ → ℂ) (w : Window 3) :
    convCoeff a (winSeqStd w) 1 = a 0 * w 1 + a 1 * w 0 := by
  classical
  simp [Hyperlocal.Cancellation.convCoeff, Hyperlocal.Cancellation.coeff,
        winSeqStd, Finset.range_succ, Finset.sum_range_succ]
  ring

@[simp] lemma convCoeff_winSeqStd_two (a : ℕ → ℂ) (w : Window 3) :
    convCoeff a (winSeqStd w) 2 = a 0 * w 2 + a 1 * w 1 + a 2 * w 0 := by
  classical
  simp [Hyperlocal.Cancellation.convCoeff, Hyperlocal.Cancellation.coeff,
        winSeqStd, Finset.range_succ, Finset.sum_range_succ]
  ring

/-!
  ### Coordinate formulas for `toeplitzR 2`.

  These are cheap now because the only “interesting” terms are `shiftR'` and
  `shiftR'(shiftR' w)` at coordinates 1/2, which are handled by the simp lemmas above.
-/

@[simp] lemma toeplitzR₂_apply0 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzR 2 coeffs) w 0 = coeffs 0 * w 0 := by
  classical
  simp [Hyperlocal.Transport.toeplitzR, Hyperlocal.Transport.shiftCombo,
        Hyperlocal.Transport.compPow, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, Hyperlocal.Transport.shiftRₗ_apply,
        Finset.range_succ, Finset.sum_range_succ]

@[simp] lemma toeplitzR₂_apply1 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzR 2 coeffs) w 1 = coeffs 0 * w 1 + coeffs 1 * w 0 := by
  classical
  simp [Hyperlocal.Transport.toeplitzR, Hyperlocal.Transport.shiftCombo,
        Hyperlocal.Transport.compPow, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, Hyperlocal.Transport.shiftRₗ_apply,
        Finset.range_succ, Finset.sum_range_succ]
  ring

@[simp] lemma toeplitzR₂_apply2 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzR 2 coeffs) w 2 = coeffs 0 * w 2 + coeffs 1 * w 1 + coeffs 2 * w 0 := by
  classical
  simp [Hyperlocal.Transport.toeplitzR, Hyperlocal.Transport.shiftCombo,
        Hyperlocal.Transport.compPow, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, Hyperlocal.Transport.shiftRₗ_apply,
        Finset.range_succ, Finset.sum_range_succ]
  ring

/-!
  ### Closed forms for the specific RHS `range`-sums that appear in the 3 cases.

  These are written to be *heartbeats-safe*: each is a direct `simp` on a tiny finite sum.
  No rewriting to `convCoeff` is used in the main lemma.
-/

@[simp] lemma rhs_sum0_closed (a : ℕ → ℂ) (w : Window 3) :
    (∑ x ∈ Finset.range 1, a x * winSeqStd w (0 - x)) = a 0 * w 0 := by
  classical
  -- range 1 = {0}
  simp [winSeqStd]

@[simp] lemma rhs_sum1_closed (a : ℕ → ℂ) (w : Window 3) :
    (∑ x ∈ Finset.range 2, a x * winSeqStd w (1 - x)) = a 0 * w 1 + a 1 * w 0 := by
  classical
  -- range 2 = {0,1}
  simp [winSeqStd, Finset.range_succ, Finset.sum_range_succ]
  ring

@[simp] lemma rhs_sum2_closed (a : ℕ → ℂ) (w : Window 3) :
    (∑ x ∈ Finset.range 3, a x * winSeqStd w (2 - x)) =
      a 0 * w 2 + a 1 * w 1 + a 2 * w 0 := by
  classical
  -- range 3 = {0,1,2}
  simp [winSeqStd, Finset.range_succ, Finset.sum_range_succ]
  ring

/--
Main lemma: reduce `XiTransportOp 2 s` to the explicit closed forms of the RHS sums.

This is the version you want as the stable micro-bridge.
-/
theorem XiTransportOp₂_apply_eq_convCoeff
    (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w = fun i : Fin 3 =>
      convCoeff (shiftCoeff (delta s)) (winSeqStd w) i.1 := by
  classical
  ext i
  fin_cases i
  · -- i = 0
    -- LHS: toeplitzR closed form
    -- RHS: convCoeff closed form at 0
    simp [XiTransportOp, convCoeff_winSeqStd_zero]
  · -- i = 1
    simp [XiTransportOp, convCoeff_winSeqStd_one]
    try ring
  · -- i = 2
    simp [XiTransportOp, convCoeff_winSeqStd_two]
    try ring


end XiTransport
end Targets
end Hyperlocal
