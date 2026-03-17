import Hyperlocal.Targets.CriticalZero_Zeta_FinalAlmostUnconditional
import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromPair25Scalars
import Hyperlocal.Transport.PrimeTrigPacket
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
Final Xi-side export from the split pair-{2,5} scalar theorem surface.
-/
theorem noOffSeed_Xi_final_of_pair25_scalars_via_corridor
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
        Hyperlocal.Transport.PrimeTrigPacket.bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    NoOffSeed Xi := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact noOffSeed_Xi_final_almost_unconditional

/-- Final ζ-side export from the same split pair-{2,5} scalar theorem surface. -/
theorem noOffSeed_Zeta_final_of_pair25_scalars_via_corridor
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
        Hyperlocal.Transport.PrimeTrigPacket.bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact noOffSeed_Zeta_final_almost_unconditional

/-- Final RH-facing export from the same split pair-{2,5} scalar theorem surface. -/
theorem criticalzero_zeta_final_of_pair25_scalars_via_corridor
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
        Hyperlocal.Transport.PrimeTrigPacket.bCoeff (σ s) (t s) (5 : ℝ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromPair25Scalars
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact criticalzero_zeta_final_almost_unconditional
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_pair25_scalars_via_corridor
#print axioms criticalzero_zeta_final_of_pair25_scalars_via_corridor

end Targets
end Hyperlocal
