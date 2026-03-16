import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranch
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
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Smaller pair-25 resonant-branch Xi-side closure surface.

Instead of assuming the local row-0 theorem

  row0Sigma s (wpAt 0 s 5) = 0

directly on the exact `log(3/2)` resonance branch, it is enough to supply the
two branch-local scalar facts

  JetQuotOp.σ2 s = 2 * delta(s)
  bCoeff (σ s) (t s) 5 = 0.

The `p = 5` row-0 zero is then produced by the closed-form bridge already proved
in `XiPrimeWitnessW1_Row0SigmaPair25`.
-/
theorem noOffSeed_Xi_via_pair25_resonant_branch_of_sigma2_eq_two_delta_and_bCoeff5_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := by
      intro s hres
      exact Hyperlocal.Targets.XiPacket.W1.row0Sigma_wpAt5_eq_zero_of_sigma2_eq_two_delta_and_bCoeff5_zero
        (s := s)
        (hσ2δ := hσ2δ_res s hres)
        (hb5 := hb5_res s hres))

/--
ζ-side transfer of the same smaller pair-25 resonant-branch surface.
-/
theorem noOffSeed_Zeta_via_pair25_resonant_branch_of_sigma2_eq_two_delta_and_bCoeff5_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_via_pair25_resonant_branch_of_sigma2_eq_two_delta_and_bCoeff5_zero
      (hσ2δ_res := hσ2δ_res) (hb5_res := hb5_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
      (hxi := hxi'))

/--
RH-facing export of the same smaller pair-25 resonant-branch surface.
-/
theorem criticalzero_zeta_via_pair25_resonant_branch_of_sigma2_eq_two_delta_and_bCoeff5_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_via_pair25_resonant_branch_of_sigma2_eq_two_delta_and_bCoeff5_zero
        (hσ2δ_res := hσ2δ_res) (hb5_res := hb5_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
