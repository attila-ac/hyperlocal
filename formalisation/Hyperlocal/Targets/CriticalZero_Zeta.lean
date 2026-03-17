import Hyperlocal.Targets.CriticalZero_Zeta_FromWp5Provider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Conclusion.OffSeedToTAC

/--
Current public ζ-side endpoint on the smallest honest remaining seam.
-/
theorem noOffSeed_Zeta
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]
    [Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact Hyperlocal.Targets.noOffSeed_Zeta_from_wp5_provider

/-- Current public RH-facing endpoint on the same seam. -/
theorem criticalzero_zeta
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]
    [Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact Hyperlocal.Targets.criticalzero_zeta_from_wp5_provider
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta
#print axioms criticalzero_zeta

end Targets
end Hyperlocal
