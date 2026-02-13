/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientEllFromOperator.lean

  Correctness fix (row-0 only):

  Earlier drafts postulated *full-window* annihilation
    toeplitzL 2 (coeffsNat3 c) (wc s) = 0
  for a nonzero stencil c. This is impossible: wc is a transported basis
  window with a nonzero tail; full ToeplitzL annihilation forces c = 0.

  This file:
    1) Keeps the explicit impossibility lemma
         toeplitzL_annihilates_wc_imp_coeffs_zero
    2) Removes the two remaining row-0 axioms, importing the *theorem* versions from:
         XiToeplitzRecurrenceJetQuotientRow0Correctness.lean
    3) Derives `ell = 0` purely algebraically from the row-0 constraints.
-/

import Hyperlocal.Transport.Determinant
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Correctness
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3

/-! ### Local helper: `ell = 0` from a nonzero Toeplitz row annihilating three real vectors -/

/--
If a nonzero row stencil `c` annihilates `reVec3(w0)`, `reVec3(wc)`, `reVec3(wp)`,
then the determinant `ell` vanishes.
-/
lemma ell_eq_zero_of_toeplitzRow3_local
    (u0 uc up : Fin 3 → ℝ) (c : Fin 3 → ℝ)
    (hc : c ≠ 0)
    (h0 : toeplitzRow3 c u0)
    (hc0 : toeplitzRow3 c uc)
    (hp : toeplitzRow3 c up) :
    Transport.ell u0 uc up = 0 := by
  classical
  refine
    Hyperlocal.Transport.Transport.ell_eq_zero_of_depRow3
      u0 uc up c hc ?_ ?_ ?_
  · simpa [toeplitzRow3] using h0
  · simpa [toeplitzRow3] using hc0
  · simpa [toeplitzRow3] using hp

/-! ### Audit: full-window annihilation of `wc` forces the stencil to be zero -/

private lemma delta_ne_zero (s : Hyperlocal.OffSeed Xi) : XiTransport.delta s ≠ 0 := by
  have : s.ρ.re - (1 : ℝ) / 2 ≠ 0 := sub_ne_zero.mpr s.hσ
  simpa [XiTransport.delta, div_eq_mul_inv] using this

private lemma delta_ne_zeroC (s : Hyperlocal.OffSeed Xi) : (XiTransport.delta s : ℂ) ≠ 0 := by
  intro h
  apply delta_ne_zero (s := s)
  exact Complex.ofReal_eq_zero.mp h

private lemma wc_fin0 (s : Hyperlocal.OffSeed Xi) : wc s (0 : Fin 3) = 0 := by
  classical
  simpa [wc_eq_basis, basisW3, e1, e2]

private lemma wc_fin1 (s : Hyperlocal.OffSeed Xi) : wc s (1 : Fin 3) = 1 := by
  classical
  simpa [wc_eq_basis, basisW3, e1, e2]

private lemma wc_fin2 (s : Hyperlocal.OffSeed Xi) : wc s (2 : Fin 3) = (XiTransport.delta s : ℂ) := by
  classical
  simpa [wc_eq_basis, basisW3, e1, e2]

/--
Full-window annihilation of `wc` by a Window-3 ToeplitzL operator forces the
stencil coefficients to be identically zero.
-/
theorem toeplitzL_annihilates_wc_imp_coeffs_zero
    (s : Hyperlocal.OffSeed Xi) (c : Fin 3 → ℝ)
    (h : toeplitzL 2 (coeffsNat3 c) (wc s) = 0) :
    c = 0 := by
  classical
  have hδ : (XiTransport.delta s : ℂ) ≠ 0 := delta_ne_zeroC (s := s)
  have hw0 : wc s (0 : Fin 3) = 0 := wc_fin0 (s := s)
  have hw1 : wc s (1 : Fin 3) = 1 := wc_fin1 (s := s)
  have hw2 : wc s (2 : Fin 3) = (XiTransport.delta s : ℂ) := wc_fin2 (s := s)

  have r2 : (toeplitzL 2 (coeffsNat3 c) (wc s)) (2 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (2 : Fin 3)) h
  have r2' : (coeffsNat3 c 0) * (wc s) (2 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin2] using r2
  have hc0c : (c (0 : Fin 3) : ℂ) = 0 := by
    have : (c (0 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [coeffsNat3_nat0, hw2] using r2'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exfalso; exact hδ h0
  have hc0 : c (0 : Fin 3) = 0 := Complex.ofReal_eq_zero.mp hc0c

  have r1 : (toeplitzL 2 (coeffsNat3 c) (wc s)) (1 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (1 : Fin 3)) h
  have r1' :
      (coeffsNat3 c 0) * (wc s) (1 : Fin 3) + (coeffsNat3 c 1) * (wc s) (2 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin1] using r1
  have hc1c : (c (1 : Fin 3) : ℂ) = 0 := by
    have : ((c (0 : Fin 3) : ℂ) * (1 : ℂ)) + (c (1 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [coeffsNat3_nat0, coeffsNat3_nat1, hw1, hw2] using r1'
    have : (c (1 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [hc0] using this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exfalso; exact hδ h1
  have hc1 : c (1 : Fin 3) = 0 := Complex.ofReal_eq_zero.mp hc1c

  have r0 : (toeplitzL 2 (coeffsNat3 c) (wc s)) (0 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (0 : Fin 3)) h
  have r0' :
      ((coeffsNat3 c 0) * (wc s) (0 : Fin 3) + (coeffsNat3 c 1) * (wc s) (1 : Fin 3)) +
        (coeffsNat3 c 2) * (wc s) (2 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin0] using r0
  have hc2c : (c (2 : Fin 3) : ℂ) = 0 := by
    have :
        ((c (0 : Fin 3) : ℂ) * (0 : ℂ) + (c (1 : Fin 3) : ℂ) * (1 : ℂ)) +
          (c (2 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [coeffsNat3_nat0, coeffsNat3_nat1, coeffsNat3_nat2, hw0, hw1, hw2] using r0'
    have : (c (2 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [hc0, hc1] using this
    rcases mul_eq_zero.mp this with h2 | h2
    · exact h2
    · exfalso; exact hδ h2
  have hc2 : c (2 : Fin 3) = 0 := Complex.ofReal_eq_zero.mp hc2c

  ext i
  fin_cases i <;> simp [hc0, hc1, hc2]

/-! ### Theorem-level `ell` output (row-0 only ⇒ row stencil ⇒ ell=0). -/

theorem xiJetQuotEllOut_fromOperator2 (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 := by
  rcases xiJetQuotToeplitzL_row0_fromOperator2 s with ⟨c2, hc2, hw0, hwc, hwp⟩
  have h0  : toeplitzRow3 c2 (reVec3 (w0 s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c2 (w0 s) hw0
  have hc  : toeplitzRow3 c2 (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c2 (wc s) hwc
  have hp  : toeplitzRow3 c2 (reVec3 (wp2 s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c2 (wp2 s) hwp
  exact
    ell_eq_zero_of_toeplitzRow3_local
      (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s))
      c2 hc2 h0 hc hp

theorem xiJetQuotEllOut_fromOperator3 (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 := by
  rcases xiJetQuotToeplitzL_row0_fromOperator3 s with ⟨c3, hc3, hw0, hwc, hwp⟩
  have h0  : toeplitzRow3 c3 (reVec3 (w0 s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c3 (w0 s) hw0
  have hc  : toeplitzRow3 c3 (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c3 (wc s) hwc
  have hp  : toeplitzRow3 c3 (reVec3 (wp3 s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c3 (wp3 s) hwp
  exact
    ell_eq_zero_of_toeplitzRow3_local
      (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s))
      c3 hc3 h0 hc hp

/-- Export name expected by `XiToeplitzRecurrenceJetQuotient.lean` (p=2). -/
theorem xiJetQuotEll_spec2_theorem (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 := by
  simpa using xiJetQuotEllOut_fromOperator2 (s := s)

/-- Export name expected by `XiToeplitzRecurrenceJetQuotient.lean` (p=3). -/
theorem xiJetQuotEll_spec3_theorem (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 := by
  simpa using xiJetQuotEllOut_fromOperator3 (s := s)


end Hyperlocal.Targets.XiPacket
