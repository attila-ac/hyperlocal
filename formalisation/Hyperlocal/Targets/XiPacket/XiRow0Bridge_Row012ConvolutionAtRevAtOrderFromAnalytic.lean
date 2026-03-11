/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic.lean

  Stable cycle-safe API endpoint:

    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic : XiRow012ConvolutionAtRevAtOrderOut m s

  This is a thin wrapper around the discharge file.

  UPDATE (2026-03-11):
  We expose an explicit-coords theorem first, and keep the historical
  provider-based endpoint as a compatibility wrapper.
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

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [A0Nonzero (s := s)]
    (HC : XiAtOrderCoords01Out m s) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge_of_coords
    (m := m) (s := s) HC

theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  classical
  letI : A0Nonzero (s := s) := by infer_instance
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge
    (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
