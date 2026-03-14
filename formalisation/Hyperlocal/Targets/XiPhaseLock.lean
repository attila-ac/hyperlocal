/-
  Hyperlocal/Targets/XiPhaseLock.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstallerFromSigmaAndRow012TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

abbrev Xi := Hyperlocal.Targets.XiPacket.Xi

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

variable
  [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
  [_root_.Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
  [_root_.Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]

/-- Mainline: `OffSeedPhaseLock Xi`. -/
theorem xi_phaseLock
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (Hyperlocal.Targets.XiPacket.routeA_G s)) (1 - s.ρ)
          + (Hyperlocal.Targets.XiPacket.JetQuotOp.σ2 s) *
              deriv (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ)
          - (Hyperlocal.Targets.XiPacket.JetQuotOp.σ3 s) *
              (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ) = 0) :
    Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi (hroute := hroute)

/-- Stage-3 bridge: build `Conclusion.OffSeedToTAC.Stage3Bridge Xi`. -/
theorem Stage3Bridge
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (Hyperlocal.Targets.XiPacket.routeA_G s)) (1 - s.ρ)
          + (Hyperlocal.Targets.XiPacket.JetQuotOp.σ2 s) *
              deriv (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ)
          - (Hyperlocal.Targets.XiPacket.JetQuotOp.σ3 s) *
              (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ) = 0) :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi := by
  exact Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) (xi_phaseLock hroute)

end Targets
end Hyperlocal
