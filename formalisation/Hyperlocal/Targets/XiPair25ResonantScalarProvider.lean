import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromPair25Scalars
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
Bundled split pair-{2,5} resonant scalar provider.

This packages the last two ordinary theorem inputs still blocking the final
unconditional closure:
  * resonant-branch sigma2 = 2 * delta
  * resonant-branch bCoeff(...,5) = 0
-/
class XiPair25ResonantScalarProvider : Prop where
  sigma2_eq_two_delta_on_resonant_branch_global :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)

  bCoeff5_zero_on_resonant_branch_global :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      bCoeff (σ s) (t s) (5 : ℝ) = 0

/--
If the standard theorem-side trio and the bundled pair-{2,5} scalar provider
are available, then the bundled final RH corridor is available.
-/
instance instXiFinalRhCorridorProviderOfPair25ResonantScalarProvider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider] :
    XiFinalRhCorridorProvider := by
  exact
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res :=
        XiPair25ResonantScalarProvider.sigma2_eq_two_delta_on_resonant_branch_global)
      (hb5_res :=
        XiPair25ResonantScalarProvider.bCoeff5_zero_on_resonant_branch_global)

end Targets
end Hyperlocal
