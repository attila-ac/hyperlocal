import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchAttempt
import Hyperlocal.Targets.XiNoOffSeedDirectFromResonantBranchSeamsTrueAnalyticJetConvolution
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
Final Xi-side closure from the resonant-branch scalar midpoint,
now honestly parameterised by the single remaining local theorem

  ∀ s, sin(t(s) * log(3/2)) = 0 -> row0Sigma s (wpAt 0 s 5) = 0.
-/
theorem noOffSeed_Xi_final_from_resonant_sigma2_eq_two_delta
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_all
      (hwp5_res := hwp5_res))

/--
Final ζ-side closure from the same single local resonant-branch theorem.
-/
theorem noOffSeed_Zeta_final_from_resonant_sigma2_eq_two_delta
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_all
      (hwp5_res := hwp5_res))

/--
Final RH-facing closure from the same single local resonant-branch theorem.
-/
theorem criticalzero_zeta_final_from_resonant_sigma2_eq_two_delta
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_all
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
