import Hyperlocal.Targets.CriticalZero_Zeta_FinalWp5ProviderGated
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket

/--
Bundled final RH corridor provider.

This is the honest current Case-2 surface:
the final wp5 endpoint still needs the standard theorem-side trio together with
the final wp5 resonant-branch provider, so we bundle exactly those four classes
into one stable consumer surface.
-/
class XiFinalRhCorridorProvider : Prop extends
    XiJetQuotRec2AtOrderTrueAnalytic,
    TAC.XiJetWindowEqAtOrderQuotProvider,
    RouteAWcScalarProvider,
    XiWp5Row0ZeroOnResonantBranchProvider

/--
If the four component providers are available explicitly, the bundled final
corridor provider is available.
-/
instance instXiFinalRhCorridorProviderOfComponents
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiWp5Row0ZeroOnResonantBranchProvider] :
    XiFinalRhCorridorProvider where
  toXiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  toXiJetWindowEqAtOrderQuotProvider := inferInstance
  toRouteAWcScalarProvider := inferInstance
  toXiWp5Row0ZeroOnResonantBranchProvider := inferInstance

/--
Final Xi-side closure on the bundled final corridor surface.
-/
theorem noOffSeed_Xi_final_of_corridor_provider
    [XiFinalRhCorridorProvider] :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  haveI : XiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  haveI : TAC.XiJetWindowEqAtOrderQuotProvider := inferInstance
  haveI : RouteAWcScalarProvider := inferInstance
  haveI : XiWp5Row0ZeroOnResonantBranchProvider := inferInstance
  exact Hyperlocal.Targets.noOffSeed_Xi_final_of_wp5_resonant_branch_provider

/--
Final ζ-side closure on the bundled final corridor surface.
-/
theorem noOffSeed_Zeta_final_of_corridor_provider
    [XiFinalRhCorridorProvider] :
    NoOffSeed Hyperlocal.zeta := by
  haveI : XiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  haveI : TAC.XiJetWindowEqAtOrderQuotProvider := inferInstance
  haveI : RouteAWcScalarProvider := inferInstance
  haveI : XiWp5Row0ZeroOnResonantBranchProvider := inferInstance
  exact Hyperlocal.Targets.noOffSeed_Zeta_final_of_wp5_resonant_branch_provider

/--
Final RH-facing closure on the bundled final corridor surface.
-/
theorem criticalzero_zeta_final_of_corridor_provider
    [XiFinalRhCorridorProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  haveI : XiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  haveI : TAC.XiJetWindowEqAtOrderQuotProvider := inferInstance
  haveI : RouteAWcScalarProvider := inferInstance
  haveI : XiWp5Row0ZeroOnResonantBranchProvider := inferInstance
  exact Hyperlocal.Targets.criticalzero_zeta_final_of_wp5_resonant_branch_provider
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
