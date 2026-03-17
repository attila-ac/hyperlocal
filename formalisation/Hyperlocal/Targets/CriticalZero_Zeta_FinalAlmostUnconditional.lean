import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket

/--
Honest final Xi-side export on the smallest currently stable consumer surface.

This is not fully unconditional yet. The dependency cone is now reduced to the
single bundled corridor provider.
-/
theorem noOffSeed_Xi_final_almost_unconditional
    [XiFinalRhCorridorProvider] :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  exact Hyperlocal.Targets.noOffSeed_Xi_final_of_corridor_provider

/-- Honest final ζ-side export on the same bundled corridor surface. -/
theorem noOffSeed_Zeta_final_almost_unconditional
    [XiFinalRhCorridorProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact Hyperlocal.Targets.noOffSeed_Zeta_final_of_corridor_provider

/--
Honest RH-facing export on the same bundled corridor surface.
-/
theorem criticalzero_zeta_final_almost_unconditional
    [XiFinalRhCorridorProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact Hyperlocal.Targets.criticalzero_zeta_final_of_corridor_provider
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
