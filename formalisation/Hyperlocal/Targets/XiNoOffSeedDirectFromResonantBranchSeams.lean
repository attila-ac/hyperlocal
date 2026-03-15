/-
  Hyperlocal/Targets/XiNoOffSeedDirectFromResonantBranchSeams.lean

  Final shrink of the remaining burden:

  the nonresonant branch is already closed by W1 localisation, so to finish the
  RH-facing chain it is enough to prove any equivalent Wc seam only on the exact
  resonance branch

      sin(t log(3/2)) = 0.

  This file packages that fact for all four useful seam surfaces:

    (A) row0Sigma s (wc s) = 0
    (B) convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0
    (C) JetQuotOp.σ2 s = 2 * delta(s)
    (D) 2 G''(1-ρ) = σ2 G'(1-ρ) - σ3 G(1-ρ)

  So after this file the true remaining theorem-family is no longer
  "prove A/B/C/D globally", but

      prove any one of A/B/C/D on the exact resonance branch only.
-/

import Hyperlocal.Targets.XiNoOffSeedDirectFromEquivalentWcSeams
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_WcEquivalentFormLocalisation
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion
open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport
open Hyperlocal.Cancellation
open scoped Real

/--
Resonant-branch version of equivalent form (A):

if you can prove `row0Sigma s (wc s) = 0` only on the exact resonance branch,
then `NoOffSeed Xi` already follows.
-/
theorem noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  have hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0 := by
    intro s
    by_cases hres :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
    · exact hsigma_res s hres
    · have htv :
          ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hres
      exact row0Sigma_wc_eq_zero_of_tval_ne_zero (s := s) htv
  exact noOffSeed_Xi_of_row0Sigma_wc_zero (hsigma := hsigma)

/--
ζ-side transfer of the same resonant-branch form (A) criterion.
-/
theorem noOffSeed_Zeta_of_row0Sigma_wc_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch
      (hsigma_res := hsigma_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
RH-facing export of the same resonant-branch form (A) criterion.
-/
theorem criticalzero_zeta_of_row0Sigma_wc_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch
        (hsigma_res := hsigma_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
Resonant-branch version of equivalent form (B).

For the nonresonant branch we already know `row0Sigma s (wc s) = 0`, hence also
the clean coeff-3 vanishing.
-/
theorem noOffSeed_Xi_of_wc_coeff3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    NoOffSeed Xi := by
  have h3 :
      ∀ s : Hyperlocal.OffSeed Xi,
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
    intro s
    by_cases hres :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
    · exact h3_res s hres
    · have htv :
          ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hres
      exact wc_convCoeff3_clean_of_row0Sigma_wc_zero
        (s := s)
        (hsigma := row0Sigma_wc_eq_zero_of_tval_ne_zero (s := s) htv)
  exact noOffSeed_Xi_of_wc_coeff3_zero (h3 := h3)

/--
ζ-side transfer of the same resonant-branch form (B) criterion.
-/
theorem noOffSeed_Zeta_of_wc_coeff3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_wc_coeff3_zero_on_resonant_branch
      (h3_res := h3_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
RH-facing export of the same resonant-branch form (B) criterion.
-/
theorem criticalzero_zeta_of_wc_coeff3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_wc_coeff3_zero_on_resonant_branch
        (h3_res := h3_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
Resonant-branch version of equivalent form (C):

if you can prove `σ2 = 2*delta` only on the exact resonance branch, then
`NoOffSeed Xi` already follows.
-/
theorem noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    NoOffSeed Xi := by
  have hσ2δ :
      ∀ s : Hyperlocal.OffSeed Xi,
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
    intro s
    by_cases hres :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
    · exact hσ2δ_res s hres
    · have htv :
          ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hres
      exact sigma2_eq_two_delta_of_tval_ne_zero (s := s) htv
  exact noOffSeed_Xi_of_sigma2_eq_two_delta (hσ2δ := hσ2δ)

/--
ζ-side transfer of the same resonant-branch form (C) criterion.
-/
theorem noOffSeed_Zeta_of_sigma2_eq_two_delta_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch
      (hσ2δ_res := hσ2δ_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
RH-facing export of the same resonant-branch form (C) criterion.
-/
theorem criticalzero_zeta_of_sigma2_eq_two_delta_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch
        (hσ2δ_res := hσ2δ_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
Resonant-branch version of equivalent form (D):

if you can prove the Route-A recurrence only on the exact resonance branch,
then `NoOffSeed Xi` already follows.
-/
theorem noOffSeed_Xi_of_routeA_recurrence_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
          2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
            =
          (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
            -
          (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) :
    NoOffSeed Xi := by
  have hrec :
      ∀ s : Hyperlocal.OffSeed Xi,
        2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
          =
        (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          -
        (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
    intro s
    by_cases hres :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
    · exact hrec_res s hres
    · have htv :
          ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hres
      exact routeA_recurrence_at_one_sub_rho_of_tval_ne_zero (s := s) htv
  exact noOffSeed_Xi_of_routeA_recurrence (hrec := hrec)

/--
ζ-side transfer of the same resonant-branch form (D) criterion.
-/
theorem noOffSeed_Zeta_of_routeA_recurrence_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
          2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
            =
          (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
            -
          (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_routeA_recurrence_on_resonant_branch
      (hrec_res := hrec_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
RH-facing export of the same resonant-branch form (D) criterion.
-/
theorem criticalzero_zeta_of_routeA_recurrence_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
          2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
            =
          (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
            -
          (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ))
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_routeA_recurrence_on_resonant_branch
        (hrec_res := hrec_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
