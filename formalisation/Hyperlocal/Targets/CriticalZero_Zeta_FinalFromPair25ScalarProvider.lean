import Hyperlocal.Targets.CriticalZero_Zeta_FinalAlmostUnconditional
import Hyperlocal.Targets.XiPair25ResonantScalarProvider
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
Final Xi-side export from the bundled pair-{2,5} resonant scalar provider.
-/
theorem noOffSeed_Xi_final_of_pair25_scalar_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider] :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact Hyperlocal.Targets.noOffSeed_Xi_final_almost_unconditional

/-- Final ζ-side export from the same bundled pair-{2,5} scalar provider. -/
theorem noOffSeed_Zeta_final_of_pair25_scalar_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact Hyperlocal.Targets.noOffSeed_Zeta_final_almost_unconditional

/-- Final RH-facing export from the same bundled pair-{2,5} scalar provider. -/
theorem criticalzero_zeta_final_of_pair25_scalar_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact Hyperlocal.Targets.criticalzero_zeta_final_almost_unconditional
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
