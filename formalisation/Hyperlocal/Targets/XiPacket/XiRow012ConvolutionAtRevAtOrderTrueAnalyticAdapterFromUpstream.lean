/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Stable installed producer for `XiRow012UpstreamTrueAnalytic`.

  UPDATE (2026-03-11):
  This adapter now consumes the theorem-level coords01 surface directly,
  via the explicit-coords Row012 analytic endpoint, instead of importing the
  fallback coords01 provider axiom.

  HONESTY FIX:
  The explicit-coords analytic endpoint also requires the theorem-side
  Route-A quotient window gate

      [TAC.XiJetWindowEqAtOrderQuotProvider]

  so this adapter must state that dependency explicitly.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

instance (priority := 1000)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012UpstreamTrueAnalytic where
  row012_out := by
    intro m s
    letI : A0Nonzero (s := s) := by infer_instance
    have HC : XiAtOrderCoords01Out m s :=
      xiAtOrderCoords01Out_theorem (m := m) (s := s)
    exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_of_coords
      (m := m) (s := s) HC

end XiPacket
end Targets
end Hyperlocal
