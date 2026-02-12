/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceToeplitzLToRow3.lean

  Bridge lemma:
    (Window-3 Toeplitz operator annihilation with real coefficients)
      ⇒ Window-3 Toeplitz row stencil on `reVec3`.

  NOTE: do NOT import `Mathlib.Algebra.BigOperators.Basic` (missing in your Mathlib pin).
-/

import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

namespace ToeplitzLToRow3

/-- Extend a real Window-3 coefficient vector to `ℕ → ℂ` (zero tail). -/
def coeffsNat3 (c : Fin 3 → ℝ) : ℕ → ℂ :=
  fun k => if hk : k < 3 then (c ⟨k, hk⟩ : ℂ) else 0

@[simp] lemma coeffsNat3_nat0 (c : Fin 3 → ℝ) : coeffsNat3 c 0 = (c (0 : Fin 3) : ℂ) := by
  classical
  simp [coeffsNat3]

@[simp] lemma coeffsNat3_nat1 (c : Fin 3 → ℝ) : coeffsNat3 c 1 = (c (1 : Fin 3) : ℂ) := by
  classical
  simp [coeffsNat3]

@[simp] lemma coeffsNat3_nat2 (c : Fin 3 → ℝ) : coeffsNat3 c 2 = (c (2 : Fin 3) : ℂ) := by
  classical
  simp [coeffsNat3]

/-- Helper: real part of `(r:ℂ) * z`. -/
@[simp] lemma re_ofReal_mul (r : ℝ) (z : ℂ) : (((r : ℂ) * z).re) = r * z.re := by
  simp [Complex.mul_re]

/-
  Key local facts: for `n=2` (Window length 3), `shiftLₗ 2` really is the left-shift
  (with a zero tail), but we only need two coordinate computations for index `0` and `1`.
-/

@[simp] lemma shiftLₗ_two_apply0 (w : Window 3) :
    (shiftLₗ 2 w) (0 : Fin 3) = w (1 : Fin 3) := by
  classical
  have hrev0 : ((0 : Fin 3).rev) = (2 : Fin 3) := by decide
  have hrev1 : ((1 : Fin 3).rev) = (1 : Fin 3) := by decide
  -- unfold `shiftLₗ` to `parity ∘ shiftR ∘ parity` and evaluate at index 0
  have : (shiftLₗ 2 w) (0 : Fin 3) = shiftR' (n := 2) (parity w) ((0 : Fin 3).rev) := by
    simp [shiftLₗ, parityₗ, shiftRₗ, LinearMap.comp_apply, parity]
  -- now use `shiftR'_succ` at `j=1` and simplify `parity`
  have hR : shiftR' (n := 2) (parity w) (2 : Fin 3) = parity w (1 : Fin 3) := by
    simpa using (shiftR'_succ (n := 2) (x := parity w) (j := (1 : Fin 2)))
  calc
    (shiftLₗ 2 w) (0 : Fin 3)
        = shiftR' (n := 2) (parity w) ((0 : Fin 3).rev) := this
    _   = shiftR' (n := 2) (parity w) (2 : Fin 3) := by simpa [hrev0]
    _   = parity w (1 : Fin 3) := hR
    _   = w ((1 : Fin 3).rev) := rfl
    _   = w (1 : Fin 3) := by simpa [hrev1]

@[simp] lemma shiftLₗ_two_apply1 (w : Window 3) :
    (shiftLₗ 2 w) (1 : Fin 3) = w (2 : Fin 3) := by
  classical
  have hrev1 : ((1 : Fin 3).rev) = (1 : Fin 3) := by decide
  have hrev0 : ((0 : Fin 3).rev) = (2 : Fin 3) := by decide
  have : (shiftLₗ 2 w) (1 : Fin 3) = shiftR' (n := 2) (parity w) ((1 : Fin 3).rev) := by
    simp [shiftLₗ, parityₗ, shiftRₗ, LinearMap.comp_apply, parity]
  have hR : shiftR' (n := 2) (parity w) (1 : Fin 3) = parity w (0 : Fin 3) := by
    simpa using (shiftR'_succ (n := 2) (x := parity w) (j := (0 : Fin 2)))
  calc
    (shiftLₗ 2 w) (1 : Fin 3)
        = shiftR' (n := 2) (parity w) ((1 : Fin 3).rev) := this
    _   = shiftR' (n := 2) (parity w) (1 : Fin 3) := by simpa [hrev1]
    _   = parity w (0 : Fin 3) := hR
    _   = w ((0 : Fin 3).rev) := rfl
    _   = w (2 : Fin 3) := by simpa [hrev0]

/--
Row-0 of `toeplitzL 2 coeffs` is the 3-term dot-product with the input window.
-/
lemma toeplitzL_two_apply_fin0 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (0 : Fin 3) =
      (coeffs 0 * w 0 + coeffs 1 * w 1) + coeffs 2 * w 2 := by
  classical
  -- The only previously-stuck subgoal was rewriting
  --   (shiftLₗ 2) ((shiftLₗ 2) w) 0
  -- which is now handled by `shiftLₗ_two_apply0_twice`.
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]


/--
If a Window-3 Toeplitz operator with *real* coefficients annihilates `w`,
then the corresponding real row stencil annihilates `reVec3 w`.
-/
lemma toeplitzRow3_reVec3_of_toeplitzL_two_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (h : toeplitzL 2 (coeffsNat3 c) w = 0) :
    toeplitzRow3 c (reVec3 w) := by
  classical
  -- take the 0th coordinate of the window equality
  have h0 : (toeplitzL 2 (coeffsNat3 c) w) (0 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (0 : Fin 3)) h

  -- rewrite row-0 as a 3-term complex dot-product
  have hsum :
      ((coeffsNat3 c 0) * w 0 + (coeffsNat3 c 1) * w 1) + (coeffsNat3 c 2) * w 2 = 0 := by
    simpa [toeplitzL_two_apply_fin0] using h0

  -- simplify the coefficients to `(c i : ℂ)` and take real parts
  have hsum' :
      (((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2) = 0 := by
    simpa using hsum

  have hre :
      ((((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2).re) = 0 := by
    simpa using congrArg Complex.re hsum'

  have hre' :
      (c (0 : Fin 3)) * (w 0).re + (c (1 : Fin 3)) * (w 1).re + (c (2 : Fin 3)) * (w 2).re = 0 := by
    -- `simp` uses `re_ofReal_mul` plus `Complex.add_re`.
    simpa [Complex.add_re, add_assoc] using hre

  -- repackage as `toeplitzRow3 c (reVec3 w)`
  simpa [toeplitzRow3, reVec3, Fin.sum_univ_three, add_assoc] using hre'

end ToeplitzLToRow3

end Hyperlocal.Targets.XiPacket
