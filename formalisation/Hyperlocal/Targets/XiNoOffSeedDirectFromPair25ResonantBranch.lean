import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
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
open scoped Real

/--
Sharper Xi-side closure surface for the pair-switch resonant branch:

the only remaining pair-25 burden is the local resonant-branch row-0 zero
for the single window `wpAt 0 s 5`.

This removes the ambient generic-prime class from the top-level pair-25
consumer and isolates the true remaining theorem target.
-/
theorem noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  have hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0 := by
    intro s
    by_cases hres :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
    · exact
        Hyperlocal.Targets.XiPacket.W1.row0Sigma_wc_eq_zero_of_resonant32_of_row0_wp5
          (s := s) (hres := hres) (hwp5 := hwp5_res s hres)
    · have htv :
          ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hres
      exact
        Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_zero_of_tval_ne_zero
          (s := s) htv
  exact noOffSeed_Xi_of_row0Sigma_wc_zero (hsigma := hsigma)

/--
ζ-side transfer of the same sharpened pair-25 surface.
-/
theorem noOffSeed_Zeta_via_pair25_resonant_branch_of_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
      (hwp5_res := hwp5_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
RH-facing export of the same sharpened pair-25 surface.
-/
theorem criticalzero_zeta_via_pair25_resonant_branch_of_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
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
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
        (hwp5_res := hwp5_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
Original class-based Xi-side closure via the second finite pair `{2,5}` on the
exact resonant branch.

This is now just a wrapper around the sharpened theorem above.
-/
theorem noOffSeed_Xi_via_pair25_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := by
      intro s hres
      rw [← toeplitzL_row0_eq_row0Sigma (s := s) (w := wpAt 0 s 5)]
      exact xiJetQuot_row0_wpAt_of_trueAnalyticPrime (m := 0) (s := s) (p := 5))

/--
Original ζ-side closure via the second finite pair `{2,5}`.
-/
theorem noOffSeed_Zeta_via_pair25_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi := noOffSeed_Xi_via_pair25_resonant_branch

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
Original RH-facing export via the second finite pair `{2,5}`.
-/
theorem criticalzero_zeta_via_pair25_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi := noOffSeed_Xi_via_pair25_resonant_branch
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
