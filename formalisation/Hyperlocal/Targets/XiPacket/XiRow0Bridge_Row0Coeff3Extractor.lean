/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Extractor.lean

  Cycle-kill extractor:
  * DO NOT import `XiToeplitzRecurrenceJetQuotientRow0Frontier`
    because that re-enters `...Row0Concrete` and closes the build cycle.
  * DO NOT import `XiToeplitzRecurrenceJetQuotientRow0FrontierSpecTheorem`
    because that sits downstream of `...Row0ConcreteExtract`, which depends back on
    this extractor.
  * Instead consume only:
      - row-0 scalar rewrite from `...Row0ConcreteProof`
      - theorem-side `w0/wp2/wp3` AtOrder proofs at `m = 0`
      - the historical public `wc` frontier wrapper
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpec
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation
open Hyperlocal.Transport

variable
  [XiJetQuotRec2AtOrderTrueAnalytic]
  [TAC.XiJetWindowEqAtOrderQuotProvider]

theorem row0ConvCoeff3_w0 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
    simpa [w0At_zero (s := s)] using
      (xiJetQuot_row0_w0At_spec_proof (m := 0) (s := s))
  have hs : row0Sigma s (w0 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0 s)] using hs

theorem row0ConvCoeff3_wc (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
    exact xiJetQuot_row0_wc_spec (s := s)
  have hs : row0Sigma s (wc s) = 0 := by
    rw [toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)] at ht
    exact ht
  rw [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)] at hs
  exact hs

theorem row0ConvCoeff3_wp2 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
    simpa [wp2At_zero (s := s)] using
      (xiJetQuot_row0_wp2At_spec_proof (m := 0) (s := s))
  have hs : row0Sigma s (wp2 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2 s)] using hs

theorem row0ConvCoeff3_wp3 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
    simpa [wp3At_zero (s := s)] using
      (xiJetQuot_row0_wp3At_spec_proof (m := 0) (s := s))
  have hs : row0Sigma s (wp3 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3 s)] using hs

end XiPacket
end Targets
end Hyperlocal
