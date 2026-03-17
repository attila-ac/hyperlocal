import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Sigma2EqTwoDeltaFromResonant32
import Hyperlocal.Targets.CriticalZero_Zeta_FinalLocalScalarTargetInterpolatedFromPair25Sigma2DeltaBCoeff5
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
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Aggressive stronger-track contraction:

once the resonant32 scalar seam is available provider-free, the only remaining
local burden is the prime-5 sine coefficient vanishing theorem

  bCoeff (σ s) (t s) 5 = 0

on the exact resonant branch.
-/
theorem sin_log2_zero_on_resonant_branch_of_resonant32_and_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  exact
    sin_log2_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := by
        intro u hu
        exact XiPacket.sigma2_eq_two_delta_of_resonant32
          (s := u) (hres := hu))
      (hb5_res := hb5_res)
      s hres

/--
Prime-3 twin: the same stronger-track contraction also yields the prime-3
resonant sine theorem from the single prime-5 coefficient burden.
-/
theorem sin_log3_zero_on_resonant_branch_of_resonant32_and_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
  intro s hres
  exact
    sin_log3_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := by
        intro u hu
        exact XiPacket.sigma2_eq_two_delta_of_resonant32
          (s := u) (hres := hu))
      (hb5_res := hb5_res)
      s hres

/--
Xi-side final export from the single stronger-track burden `hb5_res`.
-/
theorem noOffSeed_Xi_final_of_resonant32_and_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sin2_zero_on_resonant_branch
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_resonant32_and_bCoeff5
        (hb5_res := hb5_res))

/--
ζ-side final export from the single stronger-track burden `hb5_res`.
-/
theorem noOffSeed_Zeta_final_of_resonant32_and_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sin2_zero_on_resonant_branch
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_resonant32_and_bCoeff5
        (hb5_res := hb5_res))

/--
RH-facing final export from the single stronger-track burden `hb5_res`.
-/
theorem criticalzero_zeta_final_of_resonant32_and_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_sin2_zero_on_resonant_branch
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_resonant32_and_bCoeff5
        (hb5_res := hb5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
