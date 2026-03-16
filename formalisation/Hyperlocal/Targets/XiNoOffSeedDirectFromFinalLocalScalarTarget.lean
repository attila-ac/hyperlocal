import Hyperlocal.Targets.XiNoOffSeedDirectFromOnePrimeSineOnResonantBranch
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
Canonical final local scalar target (prime 2):

on the exact `log(3/2)` resonance branch, it is enough to prove

  sin(t(s) * log 2) = 0.

This is strictly smaller than the old pair-25 local target
`row0Sigma s (wpAt 0 s 5) = 0`.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sin2_zero_on_resonant_branch
    (h2_res := h2_res)

/--
ζ-side transfer of the canonical final local scalar target.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sin2_zero_on_resonant_branch
    (h2_res := h2_res)

/--
RH-facing export of the canonical final local scalar target.
-/
theorem criticalzero_zeta_of_final_local_scalar_target
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
  exact criticalzero_zeta_of_sin2_zero_on_resonant_branch
    (h2_res := h2_res) (hζ := hζ) (hIm := hIm)

/--
Symmetric prime-3 version of the same final local scalar target.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_prime3
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sin3_zero_on_resonant_branch
    (h3_res := h3_res)

/--
Symmetric prime-3 ζ-side transfer.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_prime3
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sin3_zero_on_resonant_branch
    (h3_res := h3_res)

/--
Symmetric prime-3 RH-facing export.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_prime3
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_sin3_zero_on_resonant_branch
    (h3_res := h3_res) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
