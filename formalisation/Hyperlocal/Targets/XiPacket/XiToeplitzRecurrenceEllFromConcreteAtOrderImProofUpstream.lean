/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrderImProofUpstream.lean

  Imag-pivot upstream proof module.

  LIVE WC-SPLICE:
  Keep the existing clean Rec2 route for `w0At/wp2At/wp3At`,
  but source the `wc` row-0 fact from the gated parallel producer
  `XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil`
  instead of the historical `xiJetQuot_row0_wc_spec_proof`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceStencilToEll
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3
open ToeplitzEllOutAtOrderProof

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

lemma toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero
    (c : Fin 3 → ℝ) (w : Window 3)
    (h0 : (toeplitzL 2 (coeffsNat3 c) w) (0 : Fin 3) = 0) :
    toeplitzRow3 c (imVec3 w) := by
  classical
  have hsum :
      ((coeffsNat3 c 0) * w 0 + (coeffsNat3 c 1) * w 1) + (coeffsNat3 c 2) * w 2 = 0 := by
    simpa [toeplitzL_two_apply_fin0] using h0
  have hsum' :
      (((coeffsNat3 c 0) * w 0 + (coeffsNat3 c 1) * w 1) + (coeffsNat3 c 2) * w 2) = 0 := by
    exact hsum
  have him0 :
      ((((coeffsNat3 c 0) * w 0 + (coeffsNat3 c 1) * w 1) + (coeffsNat3 c 2) * w 2).im) = 0 := by
    simpa using congrArg Complex.im hsum'
  have him :
      (c (0 : Fin 3)) * (w 0).im + (c (1 : Fin 3)) * (w 1).im + (c (2 : Fin 3)) * (w 2).im = 0 := by
    simpa [coeffsNat3_nat0, coeffsNat3_nat1, coeffsNat3_nat2,
      Complex.add_im, add_assoc, ToeplitzLToRow3.im_ofReal_mul] using him0
  have : (∑ i : Fin 3, c i * (imVec3 w) i) = 0 := by
    simpa [imVec3, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using him
  simpa [toeplitzRow3] using this

theorem xiToeplitzEllOutAtIm_fromRecurrenceC_proof
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp3At m s)) = 0 := by
  classical

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  have hc : cOp s ≠ 0 := cOp_ne_zero (s := s)

  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop

  have hw0_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (w0At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := w0At m s)
      hreal0 hreal1 hreal2 Hw.hop_w0At

  have hwc_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wc s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wc s)
      hreal0 hreal1 hreal2 (xiJetQuot_row0_wc_fromWcStencil (s := s))

  have hwp2_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wp2At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp2At m s)
      hreal0 hreal1 hreal2 Hw.hop_wp2At

  have hwp3_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wp3At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp3At m s)
      hreal0 hreal1 hreal2 Hw.hop_wp3At

  have hU0 : toeplitzRow3 (cOp s) (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero (c := cOp s) (w := w0At m s) hw0_row0

  have hUc : toeplitzRow3 (cOp s) (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wc s) hwc_row0

  have hV2 : toeplitzRow3 (cOp s) (imVec3 (wp2At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero (c := cOp s) (w := wp2At m s) hwp2_row0

  have hV3 : toeplitzRow3 (cOp s) (imVec3 (wp3At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero (c := cOp s) (w := wp3At m s) hwp3_row0

  refine ⟨?_, ?_⟩
  ·
    exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
      (u0 := imVec3 (w0At m s))
      (uc := reVec3 (wc s))
      (v := imVec3 (wp2At m s))
      (c := cOp s)
      hc hU0 hUc hV2
  ·
    exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
      (u0 := imVec3 (w0At m s))
      (uc := reVec3 (wc s))
      (v := imVec3 (wp3At m s))
      (c := cOp s)
      hc hU0 hUc hV3

theorem xiToeplitzEllOutAtImRe_fromRecurrenceC_proof
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0 := by
  classical

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  have hc : cOp s ≠ 0 := cOp_ne_zero (s := s)

  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop

  have hw0_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (w0At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := w0At m s)
      hreal0 hreal1 hreal2 Hw.hop_w0At

  have hwc_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wc s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wc s)
      hreal0 hreal1 hreal2 (xiJetQuot_row0_wc_fromWcStencil (s := s))

  have hwp2_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wp2At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp2At m s)
      hreal0 hreal1 hreal2 Hw.hop_wp2At

  have hwp3_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wp3At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp3At m s)
      hreal0 hreal1 hreal2 Hw.hop_wp3At

  have hU0 : toeplitzRow3 (cOp s) (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero (c := cOp s) (w := w0At m s) hw0_row0

  have hUc : toeplitzRow3 (cOp s) (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wc s) hwc_row0

  have hV2 : toeplitzRow3 (cOp s) (reVec3 (wp2At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wp2At m s) hwp2_row0

  have hV3 : toeplitzRow3 (cOp s) (reVec3 (wp3At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wp3At m s) hwp3_row0

  refine ⟨?_, ?_⟩
  ·
    exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
      (u0 := imVec3 (w0At m s))
      (uc := reVec3 (wc s))
      (v := reVec3 (wp2At m s))
      (c := cOp s)
      hc hU0 hUc hV2
  ·
    exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
      (u0 := imVec3 (w0At m s))
      (uc := reVec3 (wc s))
      (v := reVec3 (wp3At m s))
      (c := cOp s)
      hc hU0 hUc hV3

theorem xiToeplitzEllOutAtImRe_w0_fromRecurrenceC_proof
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s)) = 0 := by
  classical

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  have hc : cOp s ≠ 0 := cOp_ne_zero (s := s)

  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop

  have hw0_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (w0At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := w0At m s)
      hreal0 hreal1 hreal2 Hw.hop_w0At

  have hwc_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wc s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wc s)
      hreal0 hreal1 hreal2 (xiJetQuot_row0_wc_fromWcStencil (s := s))

  have hU0 : toeplitzRow3 (cOp s) (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero (c := cOp s) (w := w0At m s) hw0_row0

  have hUc : toeplitzRow3 (cOp s) (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wc s) hwc_row0

  have hV0 : toeplitzRow3 (cOp s) (reVec3 (w0At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (w0At m s) hw0_row0

  exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
    (u0 := imVec3 (w0At m s))
    (uc := reVec3 (wc s))
    (v := reVec3 (w0At m s))
    (c := cOp s)
    hc hU0 hUc hV0

end XiPacket
end Targets
end Hyperlocal
