import Hyperlocal.Targets.CriticalZero_Zeta_FinalAlmostUnconditional
import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromPair25Scalars
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
Final Xi-side export from the split pair-{2,5} scalar theorem surface.
-/
theorem noOffSeed_Xi_final_of_pair25_scalars
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
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact Hyperlocal.Targets.noOffSeed_Xi_final_almost_unconditional

/-- Final ζ-side export from the split pair-{2,5} scalar theorem surface. -/
theorem noOffSeed_Zeta_final_of_pair25_scalars
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
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact Hyperlocal.Targets.noOffSeed_Zeta_final_almost_unconditional

/-- Final RH-facing export from the split pair-{2,5} scalar theorem surface. -/
theorem criticalzero_zeta_final_of_pair25_scalars
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
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact Hyperlocal.Targets.criticalzero_zeta_final_almost_unconditional
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_pair25_scalars
#print axioms criticalzero_zeta_final_of_pair25_scalars

end Targets
end Hyperlocal
