/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3ExtractorCore.lean

  Parametric core for the four canonical coefficient-3 goals.

  POLICY:
  * keep w0/wp2/wp3 on the existing at-order proof lane
  * expose the wc branch as a pure abstract insertion point
  * do NOT import Route-A stencil files here
  * do NOT import the frontier seam here
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
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
  [RouteAWcScalarProvider]

theorem row0ConvCoeff3_w0_core (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
    simpa [w0At_zero (s := s)] using
      (xiJetQuot_row0_w0At_spec_proof (m := 0) (s := s))
  have hs : row0Sigma s (w0 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0 s)] using hs

theorem row0ConvCoeff3_wc_core
    (s : OffSeed Xi)
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  exact h3

theorem row0ConvCoeff3_wp2_core (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
    simpa [wp2At_zero (s := s)] using
      (xiJetQuot_row0_wp2At_spec_proof (m := 0) (s := s))
  have hs : row0Sigma s (wp2 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2 s)] using hs

theorem row0ConvCoeff3_wp3_core (s : OffSeed Xi) :
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
