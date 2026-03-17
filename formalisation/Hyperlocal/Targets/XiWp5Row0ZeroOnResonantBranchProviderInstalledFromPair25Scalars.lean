import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchProviderInstalled
import Hyperlocal.Targets.XiBCoeff5ZeroOnResonantBranchProviderInstalled
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderBridges
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
Installed exact final wp5 resonant-branch provider from the split pair-{2,5}
scalar theorem surface.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderInstalledFromPair25Scalars
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
    XiWp5Row0ZeroOnResonantBranchProvider := by
  letI : XiSigma2EqTwoDeltaOnResonantBranchProvider :=
    { sigma2_eq_two_delta_on_resonant_branch := hσ2δ_res }
  letI : XiBCoeff5ZeroOnResonantBranchProvider :=
    { bCoeff5_zero_on_resonant_branch := hb5_res }
  infer_instance

end Targets
end Hyperlocal
