import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderInstalledFromPair25Scalars
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Bundled final RH corridor installed from the split pair-{2,5} scalar seam.

This is the exact next shrink after the green sigma2/bCoeff5/wp5 provider
installers: it packages the final wp5 provider together with the standard
theorem-side trio into the single public corridor binder.
-/
instance instXiFinalRhCorridorProviderInstalledFromPair25Scalars
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    XiFinalRhCorridorProvider := by
  letI : XiWp5Row0ZeroOnResonantBranchProvider :=
    instXiWp5Row0ZeroOnResonantBranchProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  infer_instance

end Targets
end Hyperlocal
