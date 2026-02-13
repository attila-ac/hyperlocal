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
  Key local facts: for `n=2` (Window length 3), `shiftLₗ 2` is a left-shift with zero tail.
  We only need coordinate computations.
-/

@[simp] lemma shiftLₗ_two_apply0 (w : Window 3) :
    (shiftLₗ 2 w) (0 : Fin 3) = w (1 : Fin 3) := by
  classical
  have hrev0 : ((0 : Fin 3).rev) = (2 : Fin 3) := by decide
  have hrev1 : ((1 : Fin 3).rev) = (1 : Fin 3) := by decide
  have : (shiftLₗ 2 w) (0 : Fin 3) = shiftR' (n := 2) (parity w) ((0 : Fin 3).rev) := by
    simp [shiftLₗ, parityₗ, shiftRₗ, LinearMap.comp_apply, parity]
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

@[simp] lemma shiftLₗ_two_apply2 (w : Window 3) :
    (shiftLₗ 2 w) (2 : Fin 3) = 0 := by
  classical
  have hrev2 : ((2 : Fin 3).rev) = (0 : Fin 3) := by decide
  have h :
      (shiftLₗ 2 w) (2 : Fin 3) =
        shiftR' (n := 2) (parity w) ((2 : Fin 3).rev) := by
    simp [shiftLₗ, parityₗ, shiftRₗ, LinearMap.comp_apply, parity]
  calc
    (shiftLₗ 2 w) (2 : Fin 3)
        = shiftR' (n := 2) (parity w) ((2 : Fin 3).rev) := h
    _   = shiftR' (n := 2) (parity w) (0 : Fin 3) := by simpa [hrev2]
    _   = 0 := by simpa using (shiftR'_zero (n := 2) (x := parity w))

/-- Row-0 of `toeplitzL 2 coeffs` is the 3-term dot-product with the input window. -/
lemma toeplitzL_two_apply_fin0 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (0 : Fin 3) =
      (coeffs 0 * w 0 + coeffs 1 * w 1) + coeffs 2 * w 2 := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]

/-- Row-1 of `toeplitzL 2 coeffs` only sees the tail of the input window. -/
lemma toeplitzL_two_apply_fin1 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (1 : Fin 3) =
      (coeffs 0 * w 1) + (coeffs 1 * w 2) := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]

/-- Row-2 of `toeplitzL 2 coeffs` only sees the last coordinate of the input window. -/
lemma toeplitzL_two_apply_fin2 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (2 : Fin 3) = (coeffs 0 * w 2) := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]

/--
NEW bridge:

If row-0/coordinate-0 of `toeplitzL 2 (coeffsNat3 c) w` vanishes,
then `toeplitzRow3 c (reVec3 w)` holds.
-/
lemma toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (h0 : (toeplitzL 2 (coeffsNat3 c) w) (0 : Fin 3) = 0) :
    toeplitzRow3 c (reVec3 w) := by
  classical
  have hsum :
      ((coeffsNat3 c 0) * w 0 + (coeffsNat3 c 1) * w 1) + (coeffsNat3 c 2) * w 2 = 0 := by
    simpa [toeplitzL_two_apply_fin0] using h0

  have hsum' :
      (((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2) = 0 := by
    simpa [coeffsNat3_nat0, coeffsNat3_nat1, coeffsNat3_nat2, add_assoc] using hsum

  have hre0 :
      ((((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2).re) = 0 := by
    simpa using congrArg Complex.re hsum'

  have hre :
      (c (0 : Fin 3)) * (w 0).re + (c (1 : Fin 3)) * (w 1).re + (c (2 : Fin 3)) * (w 2).re = 0 := by
    simpa [Complex.add_re, add_assoc, re_ofReal_mul] using hre0

  -- rewrite as the Fin-sum form in `toeplitzRow3`
  have :
      (∑ i : Fin 3, c i * (reVec3 w) i) = 0 := by
    -- `reVec3 w i = (w i).re`
    simpa [reVec3, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using hre

  simpa [toeplitzRow3] using this

/-- Backward-compatible old bridge: full window equality implies row-0 equality. -/
lemma toeplitzRow3_reVec3_of_toeplitzL_two_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (h : toeplitzL 2 (coeffsNat3 c) w = 0) :
    toeplitzRow3 c (reVec3 w) := by
  have h0 : (toeplitzL 2 (coeffsNat3 c) w) (0 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (0 : Fin 3)) h
  exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c w h0

end ToeplitzLToRow3

-- Export the intended downstream API so other files can use the lemmas unqualified.
export ToeplitzLToRow3
  ( coeffsNat3
    coeffsNat3_nat0 coeffsNat3_nat1 coeffsNat3_nat2
    toeplitzL_two_apply_fin0 toeplitzL_two_apply_fin1 toeplitzL_two_apply_fin2
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero
    toeplitzRow3_reVec3_of_toeplitzL_two_eq_zero )

end Hyperlocal.Targets.XiPacket
