/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceToeplitzLToRow3.lean

  Bridge lemma(s):
    (Window-3 Toeplitz operator annihilation with real coefficients)
      ⇒ Window-3 Toeplitz row stencil on `reVec3` and `imVec3`.

  This file now contains:
  * the original toeplitzL row expansions (fin0/fin1/fin2),
  * the ToeplitzR/parity transport route (theorem-level),
  * a theorem-level expansion of toeplitzR at index 2 (n=2),
  * theorem-level bridges to `toeplitzRow3` for both `reVec3` and `imVec3`.

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

@[simp] lemma coeffsNat3_nat0 (c : Fin 3 → ℝ) :
    coeffsNat3 c 0 = (c (0 : Fin 3) : ℂ) := by
  classical
  simp [coeffsNat3]

@[simp] lemma coeffsNat3_nat1 (c : Fin 3 → ℝ) :
    coeffsNat3 c 1 = (c (1 : Fin 3) : ℂ) := by
  classical
  simp [coeffsNat3]

@[simp] lemma coeffsNat3_nat2 (c : Fin 3 → ℝ) :
    coeffsNat3 c 2 = (c (2 : Fin 3) : ℂ) := by
  classical
  simp [coeffsNat3]

/-- Real part of `(r:ℂ) * z`. -/
@[simp] lemma re_ofReal_mul (r : ℝ) (z : ℂ) : (((r : ℂ) * z).re) = r * z.re := by
  simp [Complex.mul_re]

/-- Imag part of `(r:ℂ) * z`. -/
@[simp] lemma im_ofReal_mul (r : ℝ) (z : ℂ) : (((r : ℂ) * z).im) = r * z.im := by
  simp [Complex.mul_im]

/-
  Key local facts: for `n=2` (Window length 3), `shiftLₗ 2` is a left-shift with zero tail.
  We keep the original coordinate computations because downstream may rely on them.
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
        add_left_comm, add_comm]

/-- Row-2 of `toeplitzL 2 coeffs` only sees the last coordinate of the input window. -/
lemma toeplitzL_two_apply_fin2 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (2 : Fin 3) = (coeffs 0 * w 2) := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_left_comm, add_comm]

/-!
  ## Parity facts (Window 3)
-/

lemma parity_involutive_window3 (w : Window 3) : parity (parity w) = w := by
  classical
  funext i
  fin_cases i <;> simp [parity]

lemma parity_zero_window3 : parity (0 : Window 3) = 0 := by
  classical
  funext i
  fin_cases i <;> simp [parity]

lemma parity_eq_zero_iff_window3 (w : Window 3) : parity w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have := congrArg parity h
    simpa [parity_involutive_window3, parity_zero_window3] using this
  · intro h
    simpa [h, parity_zero_window3]

/-!
  ## Transport: toeplitzL=0 ⇒ toeplitzR(parity w)=0  (theorem-level)
-/
lemma toeplitzR_two_parity_eq_zero_of_toeplitzL_two_eq_zero
    (coeffs : ℕ → ℂ) (w : Window 3)
    (hL : toeplitzL 2 coeffs w = 0) :
    toeplitzR 2 coeffs (parity w) = 0 := by
  classical
  let u : Window 3 := parity w

  have hOp :
      (parityₗ 2).comp (toeplitzR 2 coeffs)
        = (toeplitzL 2 coeffs).comp (parityₗ 2) :=
    parityₗ_comp_toeplitzR (n := 2) (coeffs := coeffs)

  have hApp := congrArg (fun T : EndW 2 => T u) hOp

  have hPar :
      parity ((toeplitzR 2 coeffs) u) = (toeplitzL 2 coeffs) (parity u) := by
    simpa [LinearMap.comp_apply, parityₗ_apply] using hApp

  have hu : parity u = w := by
    simpa [u, parity_involutive_window3]

  have hPar0 : parity ((toeplitzR 2 coeffs) u) = 0 := by
    simpa [hPar, hu] using hL

  have hz : (toeplitzR 2 coeffs) u = 0 :=
    (parity_eq_zero_iff_window3 (w := (toeplitzR 2 coeffs) u)).1 hPar0

  simpa [u] using hz

/-!
  ## Explicit `shiftR'` coordinates for Window 3 (n = 2)

  We avoid `shiftRₗ_*` lemmas as rewrite lemmas, because `simp [shiftRₗ_apply]` can
  simplify those statements away to `True` in some contexts.
-/

@[simp] lemma shiftR'_apply_fin0 (w : Window 3) :
    shiftR' (n := 2) w (0 : Fin 3) = 0 := by
  simpa using (shiftR'_zero (n := 2) (x := w))

@[simp] lemma shiftR'_apply_fin1 (w : Window 3) :
    shiftR' (n := 2) w (1 : Fin 3) = w (0 : Fin 3) := by
  -- for j = 0 : Fin 2, j.succ is definitional `1 : Fin 3`.
  simpa using (shiftR'_succ (n := 2) (x := w) (j := (0 : Fin 2)))

@[simp] lemma shiftR'_apply_fin2 (w : Window 3) :
    shiftR' (n := 2) w (2 : Fin 3) = w (1 : Fin 3) := by
  simpa using (shiftR'_succ (n := 2) (x := w) (j := (1 : Fin 2)))

@[simp] lemma shiftR'_shift_apply_fin2 (w : Window 3) :
    shiftR' (n := 2) (shiftR' (n := 2) w) (2 : Fin 3) = w (0 : Fin 3) := by
  simp

/-!
  ## Expand toeplitzR at index 2 (n = 2)  (theorem-level)
-/
set_option maxRecDepth 4096 in
lemma toeplitzR_two_apply_fin2 (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzR 2 coeffs w) (2 : Fin 3)
      =
    ((coeffs 0 * w (2 : Fin 3)) + (coeffs 1 * w (1 : Fin 3))) + (coeffs 2 * w (0 : Fin 3)) := by
  classical
  simp [toeplitzR, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        shiftRₗ_apply, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm]
  try ring

/-! Parity coordinates for Window 3 (safe; we only unfold parity here). -/
@[simp] lemma parity_apply_fin0 (w : Window 3) :
    parity w (0 : Fin 3) = w (2 : Fin 3) := by
  classical
  simp [parity]

@[simp] lemma parity_apply_fin1 (w : Window 3) :
    parity w (1 : Fin 3) = w (1 : Fin 3) := by
  classical
  simp [parity]

@[simp] lemma parity_apply_fin2 (w : Window 3) :
    parity w (2 : Fin 3) = w (0 : Fin 3) := by
  classical
  simp [parity]

/--
Original-style bridge (row-0 only):

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

  have :
      (∑ i : Fin 3, c i * (reVec3 w) i) = 0 := by
    simpa [reVec3, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using hre

  simpa [toeplitzRow3] using this

/--
New bridge (full-window, ToeplitzR/parity route):

If `toeplitzL 2 (coeffsNat3 c) w = 0`, then `toeplitzRow3 c (reVec3 w)`.
-/
lemma toeplitzRow3_reVec3_of_toeplitzL_two_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (hL : toeplitzL 2 (coeffsNat3 c) w = 0) :
    toeplitzRow3 c (reVec3 w) := by
  classical
  have hR : toeplitzR 2 (coeffsNat3 c) (parity w) = 0 :=
    toeplitzR_two_parity_eq_zero_of_toeplitzL_two_eq_zero (coeffs := coeffsNat3 c) (w := w) hL

  have h2 : (toeplitzR 2 (coeffsNat3 c) (parity w)) (2 : Fin 3) = 0 := by
    simpa [hR]

  have hsum :
      ((coeffsNat3 c 0 * (parity w) (2 : Fin 3)) + (coeffsNat3 c 1 * (parity w) (1 : Fin 3)))
        + (coeffsNat3 c 2 * (parity w) (0 : Fin 3)) = 0 := by
    simpa [toeplitzR_two_apply_fin2, add_assoc] using h2

  have hsum' :
      (((c (0 : Fin 3) : ℂ) * w (0 : Fin 3) + (c (1 : Fin 3) : ℂ) * w (1 : Fin 3))
        + (c (2 : Fin 3) : ℂ) * w (2 : Fin 3)) = 0 := by
    simpa [coeffsNat3_nat0, coeffsNat3_nat1, coeffsNat3_nat2,
           parity_apply_fin0, parity_apply_fin1, parity_apply_fin2,
           add_assoc, add_left_comm, add_comm] using hsum

  have hre0 :
      ((((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2).re) = 0 := by
    simpa using congrArg Complex.re hsum'

  have hre :
      (c (0 : Fin 3)) * (w 0).re + (c (1 : Fin 3)) * (w 1).re + (c (2 : Fin 3)) * (w 2).re = 0 := by
    simpa [Complex.add_re, add_assoc, re_ofReal_mul] using hre0

  have : (∑ i : Fin 3, c i * (reVec3 w) i) = 0 := by
    simpa [reVec3, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using hre

  simpa [toeplitzRow3] using this

/--
New bridge (full-window, ToeplitzR/parity route):

If `toeplitzL 2 (coeffsNat3 c) w = 0`, then `toeplitzRow3 c (imVec3 w)`.
-/
lemma toeplitzRow3_imVec3_of_toeplitzL_two_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (hL : toeplitzL 2 (coeffsNat3 c) w = 0) :
    toeplitzRow3 c (imVec3 w) := by
  classical
  have hR : toeplitzR 2 (coeffsNat3 c) (parity w) = 0 :=
    toeplitzR_two_parity_eq_zero_of_toeplitzL_two_eq_zero (coeffs := coeffsNat3 c) (w := w) hL

  have h2 : (toeplitzR 2 (coeffsNat3 c) (parity w)) (2 : Fin 3) = 0 := by
    simpa [hR]

  have hsum :
      ((coeffsNat3 c 0 * (parity w) (2 : Fin 3)) + (coeffsNat3 c 1 * (parity w) (1 : Fin 3)))
        + (coeffsNat3 c 2 * (parity w) (0 : Fin 3)) = 0 := by
    simpa [toeplitzR_two_apply_fin2, add_assoc] using h2

  have hsum' :
      (((c (0 : Fin 3) : ℂ) * w (0 : Fin 3) + (c (1 : Fin 3) : ℂ) * w (1 : Fin 3))
        + (c (2 : Fin 3) : ℂ) * w (2 : Fin 3)) = 0 := by
    simpa [coeffsNat3_nat0, coeffsNat3_nat1, coeffsNat3_nat2,
           parity_apply_fin0, parity_apply_fin1, parity_apply_fin2,
           add_assoc, add_left_comm, add_comm] using hsum

  have him0 :
      ((((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2).im) = 0 := by
    simpa using congrArg Complex.im hsum'

  have him :
      (c (0 : Fin 3)) * (w 0).im + (c (1 : Fin 3)) * (w 1).im + (c (2 : Fin 3)) * (w 2).im = 0 := by
    simpa [Complex.add_im, add_assoc, im_ofReal_mul] using him0

  have : (∑ i : Fin 3, c i * (imVec3 w) i) = 0 := by
    simpa [imVec3, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using him

  simpa [toeplitzRow3] using this

end ToeplitzLToRow3

-- Export the intended downstream API so other files can use the lemmas unqualified.
export ToeplitzLToRow3
  ( coeffsNat3
    coeffsNat3_nat0 coeffsNat3_nat1 coeffsNat3_nat2
    toeplitzL_two_apply_fin0 toeplitzL_two_apply_fin1 toeplitzL_two_apply_fin2
    toeplitzR_two_apply_fin2
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero
    toeplitzRow3_reVec3_of_toeplitzL_two_eq_zero
    toeplitzRow3_imVec3_of_toeplitzL_two_eq_zero )

end Hyperlocal.Targets.XiPacket
