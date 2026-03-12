/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic.lean

  Stable cycle-safe API endpoint:

    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic : XiRow012ConvolutionAtRevAtOrderOut m s

  This is a thin wrapper around the discharge file.

  UPDATE (2026-03-11):
  We expose an explicit-coords theorem first, and keep the historical
  provider-based endpoint as a compatibility wrapper.

  IMPORTANT (2026-03-11, honesty fix):
  The discharge corridor now depends on the theorem-side Route-A quotient window gate

      [TAC.XiJetWindowEqAtOrderQuotProvider]

  via `XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem`.

  Therefore this wrapper must thread that gate explicitly as well.
-/
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Discharge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (HC : XiAtOrderCoords01Out m s) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge_of_coords
    (m := m) (s := s) HC

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge
    (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
