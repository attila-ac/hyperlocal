/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Extractor.lean

  Cycle-safe extractor for the four canonical coefficient-3 goals.

  POLICY:
  * w0/wp2/wp3 come from the parametric core
  * wc is currently supplied by the Route-A scalar wrapper
  * that wrapper is intentionally tiny, so a future independent wc theorem
    can replace it with a one-line swap
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3ExtractorCore
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3WcRouteANormalForm
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero
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

theorem row0ConvCoeff3_w0 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 := by
  simpa using row0ConvCoeff3_w0_core (s := s)

theorem row0ConvCoeff3_wc (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  exact
    row0ConvCoeff3_wc_core
      (s := s)
      (h3 :=
        row0ConvCoeff3_wc_of_routeA_scalar
          (s := s)
          (hroute := routeA_stencil_zero (s := s)))

theorem row0ConvCoeff3_wp2 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 := by
  simpa using row0ConvCoeff3_wp2_core (s := s)

theorem row0ConvCoeff3_wp3 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0 := by
  simpa using row0ConvCoeff3_wp3_core (s := s)

end XiPacket
end Targets
end Hyperlocal
