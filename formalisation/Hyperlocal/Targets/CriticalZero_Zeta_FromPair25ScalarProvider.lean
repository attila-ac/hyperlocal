import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromPair25ScalarProvider
import Hyperlocal.Targets.XiPair25ResonantScalarProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Conclusion.OffSeedToTAC

/--
Public ζ-side export on the bundled pair-{2,5} resonant scalar seam.
-/
theorem noOffSeed_Zeta_from_pair25_scalar_provider
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact Hyperlocal.Targets.noOffSeed_Zeta_final_of_pair25_scalar_provider

/-- Public RH-facing export on the same seam. -/
theorem criticalzero_zeta_from_pair25_scalar_provider
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact Hyperlocal.Targets.criticalzero_zeta_final_of_pair25_scalar_provider
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_from_pair25_scalar_provider
#print axioms criticalzero_zeta_from_pair25_scalar_provider

end Targets
end Hyperlocal
