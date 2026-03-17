import Hyperlocal.Targets.CriticalZero_Zeta_FinalAlmostUnconditional
import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromSin2Theorem
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
open scoped Real

/--
Final Xi-side export from the single prime-2 resonant sine theorem gate,
routed through the bundled final corridor installer.
-/
theorem noOffSeed_Xi_final_of_sin2_theorem_via_corridor
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Xi := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromSin2Theorem
      (h2_res := h2_res)
  exact noOffSeed_Xi_final_almost_unconditional

/-- Final ζ-side export from the same single prime-2 resonant sine theorem. -/
theorem noOffSeed_Zeta_final_of_sin2_theorem_via_corridor
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromSin2Theorem
      (h2_res := h2_res)
  exact noOffSeed_Zeta_final_almost_unconditional

/-- Final RH-facing export from the same single prime-2 resonant sine theorem. -/
theorem criticalzero_zeta_final_of_sin2_theorem_via_corridor
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromSin2Theorem
      (h2_res := h2_res)
  exact criticalzero_zeta_final_almost_unconditional
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_sin2_theorem_via_corridor
#print axioms criticalzero_zeta_final_of_sin2_theorem_via_corridor

end Targets
end Hyperlocal
