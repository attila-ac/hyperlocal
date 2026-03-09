/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream.lean

  Upstream proof module for AtOrder ell-out.

  IMPORTANT (cycle breaker):
  This file should consume the clean explicit Row0 witness route for the at-order
  trio `w0At/wp2At/wp3At`, while still using the theorem-level `wc` proof.

  CLEAN ROUTE USED HERE:
    Row012Upstream -> Rec2 -> OpZero_of_rec2 -> Row0Witness_of_opZero
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceStencilToEll
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream
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

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

namespace ToeplitzEllOutAtOrderProof

def cOp (s : Hyperlocal.OffSeed Xi) : Fin 3 → ℝ :=
  fun i => (JetQuotOp.aRk1 s i.1).re

lemma complex_eq_ofReal_of_im_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

lemma toeplitzL_row0_eq_of_real_coeffs
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h0 : (JetQuotOp.aRk1 s 0).im = 0)
    (h1 : (JetQuotOp.aRk1 s 1).im = 0)
    (h2 : (JetQuotOp.aRk1 s 2).im = 0) :
    (toeplitzL 2 (coeffsNat3 (cOp s)) w) (0 : Fin 3)
      = (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) := by
  have hz0 : (coeffsNat3 (cOp s) 0) = JetQuotOp.aRk1 s 0 := by
    have : ((JetQuotOp.aRk1 s 0).re : ℂ) = JetQuotOp.aRk1 s 0 := by
      simpa using (complex_eq_ofReal_of_im_zero (JetQuotOp.aRk1 s 0) h0).symm
    simpa [coeffsNat3_nat0, cOp] using this
  have hz1 : (coeffsNat3 (cOp s) 1) = JetQuotOp.aRk1 s 1 := by
    have : ((JetQuotOp.aRk1 s 1).re : ℂ) = JetQuotOp.aRk1 s 1 := by
      simpa using (complex_eq_ofReal_of_im_zero (JetQuotOp.aRk1 s 1) h1).symm
    simpa [coeffsNat3_nat1, cOp] using this
  have hz2 : (coeffsNat3 (cOp s) 2) = JetQuotOp.aRk1 s 2 := by
    have : ((JetQuotOp.aRk1 s 2).re : ℂ) = JetQuotOp.aRk1 s 2 := by
      simpa using (complex_eq_ofReal_of_im_zero (JetQuotOp.aRk1 s 2) h2).symm
    simpa [coeffsNat3_nat2, cOp] using this
  classical
  simp [toeplitzL_two_apply_fin0, hz0, hz1, hz2, add_assoc, add_left_comm, add_comm]

lemma row0_eq_zero_of_op_row0_eq_zero
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h0 : (JetQuotOp.aRk1 s 0).im = 0)
    (h1 : (JetQuotOp.aRk1 s 1).im = 0)
    (h2 : (JetQuotOp.aRk1 s 2).im = 0)
    (hop : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0) :
    (toeplitzL 2 (coeffsNat3 (cOp s)) w) (0 : Fin 3) = 0 := by
  have heq := toeplitzL_row0_eq_of_real_coeffs (s := s) (w := w) h0 h1 h2
  calc
    (toeplitzL 2 (coeffsNat3 (cOp s)) w) (0 : Fin 3)
        = (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) := by
            simpa using heq
    _ = 0 := hop

lemma cOp_ne_zero (s : Hyperlocal.OffSeed Xi) : cOp s ≠ 0 := by
  intro hc
  have hcre : cOp s (2 : Fin 3) = 0 := by
    simpa using congrArg (fun f => f (2 : Fin 3)) hc
  have hre : (JetQuotOp.aRk1 s 2).re = 0 := by
    simpa [cOp] using hcre
  have hz : JetQuotOp.aRk1 s 2 = (-2 : ℂ) := JetQuotOp.aRk1_nat2_eq_neg_two (s := s)
  have : ((-2 : ℂ).re) = 0 := by
    simpa [hz] using hre
  simpa using (by
    have : ((-2 : ℂ).re) = (-2 : ℝ) := by simp
    linarith)

end ToeplitzEllOutAtOrderProof

open ToeplitzEllOutAtOrderProof

theorem xiToeplitzEllOutAt_fromRecurrenceC_proof
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOutAt m s := by
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
      hreal0 hreal1 hreal2 (xiJetQuot_row0_wc_spec_proof (s := s))

  have hwp2_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wp2At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp2At m s)
      hreal0 hreal1 hreal2 Hw.hop_wp2At

  have hwp3_row0 : (toeplitzL 2 (coeffsNat3 (cOp s)) (wp3At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp3At m s)
      hreal0 hreal1 hreal2 Hw.hop_wp3At

  have hU0 : toeplitzRow3 (cOp s) (reVec3 (w0At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (w0At m s) hw0_row0
  have hUc : toeplitzRow3 (cOp s) (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wc s) hwc_row0
  have hV2 : toeplitzRow3 (cOp s) (reVec3 (wp2At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wp2At m s) hwp2_row0
  have hV3 : toeplitzRow3 (cOp s) (reVec3 (wp3At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wp3At m s) hwp3_row0

  refine ⟨?_, ?_⟩
  ·
    exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
      (u0 := reVec3 (w0At m s))
      (uc := reVec3 (wc s))
      (v := reVec3 (wp2At m s))
      (c := cOp s)
      hc hU0 hUc hV2
  ·
    exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
      (u0 := reVec3 (w0At m s))
      (uc := reVec3 (wc s))
      (v := reVec3 (wp3At m s))
      (c := cOp s)
      hc hU0 hUc hV3

end XiPacket
end Targets
end Hyperlocal
