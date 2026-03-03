/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrderIm.lean

  Imag-pivot analogue of `XiToeplitzRecurrenceEllFromConcreteAtOrder`:

  Using the same real Toeplitz stencil `c`, we transport row-0 constraints
  to `toeplitzRow3` constraints on `imVec3`, and conclude ell-out for the
  imag-pivot columns.

  This is theorem-only.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Fin0-only bridge for imag parts (local to this file):

If row-0/coordinate-0 of `toeplitzL 2 (coeffsNat3 c) w` vanishes,
then `toeplitzRow3 c (imVec3 w)` holds.
-/
lemma toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (h0 : (toeplitzL 2 (coeffsNat3 c) w) (0 : Fin 3) = 0) :
    toeplitzRow3 c (imVec3 w) := by
  classical
  have hsum :
      ((coeffsNat3 c 0) * w 0 + (coeffsNat3 c 1) * w 1) + (coeffsNat3 c 2) * w 2 = 0 := by
    simpa [toeplitzL_two_apply_fin0] using h0

  have hsum' :
      (((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2) = 0 := by
    simpa [coeffsNat3_nat0, coeffsNat3_nat1, coeffsNat3_nat2, add_assoc] using hsum

  have him0 :
      ((((c (0 : Fin 3) : ℂ) * w 0 + (c (1 : Fin 3) : ℂ) * w 1) + (c (2 : Fin 3) : ℂ) * w 2).im) = 0 := by
    simpa using congrArg Complex.im hsum'

  have him :
      (c (0 : Fin 3)) * (w 0).im + (c (1 : Fin 3)) * (w 1).im + (c (2 : Fin 3)) * (w 2).im = 0 := by
    -- `im_ofReal_mul` lives in `ToeplitzLToRow3` and is not exported.
    simpa [Complex.add_im, add_assoc, ToeplitzLToRow3.im_ofReal_mul] using him0

  have : (∑ i : Fin 3, c i * (imVec3 w) i) = 0 := by
    simpa [imVec3, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using him

  simpa [toeplitzRow3] using this

/--
Ell-out at order `m` for the imag-pivot columns:
`u0 = imVec3(w0At m s)`, `uc = reVec3(wc s)`,
and `up = imVec3(wp2At/wp3At m s)`.
-/
theorem xiToeplitzEllOutAtIm_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp3At m s)) = 0 := by
  classical

  -- Same witness used by the real proof (row-0 operator annihilation at the anchor windows).
  have hC : _root_.Hyperlocal.Targets.XiPacket.XiJetQuotRow0WitnessC s :=
    _root_.Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessC (s := s)

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)
  have ha2 : JetQuotOp.aRk1 s 2 ≠ 0 := JetQuotOp.aRk1_nat2_ne_zero (s := s)

  let c : Fin 3 → ℝ := JetQuotRow0.cOp s
  have hc : c ≠ 0 :=
    JetQuotRow0.cOp_ne_zero_of_aRk1_nonzero_at (s := s) (j := (2 : Fin 3)) hreal2 ha2

  -- Convert op-row0 annihilation (with coeffs `aRk1`) into toeplitzL-row0 with coeffsNat3(cOp).
  have hw0 : (toeplitzL 2 (coeffsNat3 c) (w0At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := w0At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_w0At m s)

  have hwc : (toeplitzL 2 (coeffsNat3 c) (wc s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wc s) hreal0 hreal1 hreal2 hC.hop_wc

  have hwp2 : (toeplitzL 2 (coeffsNat3 c) (wp2At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wp2At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_wp2At m s)

  have hwp3 : (toeplitzL 2 (coeffsNat3 c) (wp3At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wp3At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_wp3At m s)

  -- Transport fin0 row constraints to toeplitzRow3 constraints.
  have t0 : toeplitzRow3 c (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero c (w0At m s) hw0

  have tc : toeplitzRow3 c (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wc s) hwc

  have t2 : toeplitzRow3 c (imVec3 (wp2At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero c (wp2At m s) hwp2

  have t3 : toeplitzRow3 c (imVec3 (wp3At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero c (wp3At m s) hwp3

  refine ⟨?_, ?_⟩
  ·
    exact
      ell_eq_zero_of_toeplitzRow3_local
        (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp2At m s))
        c hc t0 tc t2
  ·
    exact
      ell_eq_zero_of_toeplitzRow3_local
        (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp3At m s))
        c hc t0 tc t3


/-
  ADDITIONS to:
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrderIm.lean
-/

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Ell-out at order `m` for the *mixed* imag-pivot configuration needed by the pivot-gate consumer:

`u0 = imVec3(w0At m s)`, `uc = reVec3(wc s)`, and `up = reVec3(wp2At/wp3At m s)`.

This is theorem-only (same witness `cOp` as the real proof).
-/
theorem xiToeplitzEllOutAtImRe_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0 := by
  classical

  have hC : _root_.Hyperlocal.Targets.XiPacket.XiJetQuotRow0WitnessC s :=
    _root_.Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessC (s := s)

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)
  have ha2 : JetQuotOp.aRk1 s 2 ≠ 0 := JetQuotOp.aRk1_nat2_ne_zero (s := s)

  let c : Fin 3 → ℝ := JetQuotRow0.cOp s
  have hc : c ≠ 0 :=
    JetQuotRow0.cOp_ne_zero_of_aRk1_nonzero_at (s := s) (j := (2 : Fin 3)) hreal2 ha2

  have hw0 : (toeplitzL 2 (coeffsNat3 c) (w0At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := w0At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_w0At m s)

  have hwc : (toeplitzL 2 (coeffsNat3 c) (wc s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wc s) hreal0 hreal1 hreal2 hC.hop_wc

  have hwp2 : (toeplitzL 2 (coeffsNat3 c) (wp2At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wp2At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_wp2At m s)

  have hwp3 : (toeplitzL 2 (coeffsNat3 c) (wp3At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wp3At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_wp3At m s)

  have t0 : toeplitzRow3 c (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero c (w0At m s) hw0

  have tc : toeplitzRow3 c (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wc s) hwc

  have t2 : toeplitzRow3 c (reVec3 (wp2At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wp2At m s) hwp2

  have t3 : toeplitzRow3 c (reVec3 (wp3At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wp3At m s) hwp3

  refine ⟨?_, ?_⟩
  ·
    exact
      ell_eq_zero_of_toeplitzRow3_local
        (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
        c hc t0 tc t2
  ·
    exact
      ell_eq_zero_of_toeplitzRow3_local
        (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
        c hc t0 tc t3

/--
Auxiliary ell-out at order `m` for the mixed configuration with `up = reVec3(w0At m s)`.

Used to cancel the `reVec3(w0At)` contribution when expanding `reVec3(wp2At/wp3At)`.
-/
theorem xiToeplitzEllOutAtImRe_w0_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s)) = 0 := by
  classical

  have hC : _root_.Hyperlocal.Targets.XiPacket.XiJetQuotRow0WitnessC s :=
    _root_.Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessC (s := s)

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)
  have ha2 : JetQuotOp.aRk1 s 2 ≠ 0 := JetQuotOp.aRk1_nat2_ne_zero (s := s)

  let c : Fin 3 → ℝ := JetQuotRow0.cOp s
  have hc : c ≠ 0 :=
    JetQuotRow0.cOp_ne_zero_of_aRk1_nonzero_at (s := s) (j := (2 : Fin 3)) hreal2 ha2

  have hw0 : (toeplitzL 2 (coeffsNat3 c) (w0At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := w0At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_w0At m s)

  have hwc : (toeplitzL 2 (coeffsNat3 c) (wc s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wc s) hreal0 hreal1 hreal2 hC.hop_wc

  have t0 : toeplitzRow3 c (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero c (w0At m s) hw0

  have tc : toeplitzRow3 c (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wc s) hwc

  have tr0 : toeplitzRow3 c (reVec3 (w0At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (w0At m s) hw0

  exact
    ell_eq_zero_of_toeplitzRow3_local
      (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s))
      c hc t0 tc tr0

end XiPacket
end Targets
end Hyperlocal

end XiPacket
end Targets
end Hyperlocal
