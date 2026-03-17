import Hyperlocal.Targets.CriticalZero_Zeta_Pair25TheoremGated
import Hyperlocal.Targets.XiNoOffSeedDirectFromFinalLocalScalarTarget
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
Prime-2 interpolation from the sharper pair-{2,5} theorem surface

  σ2 = 2 * delta
  bCoeff(...,5) = 0

with no generic-prime class anywhere.
-/
theorem sin_log2_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
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
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_pair25_sigma2delta_bCoeff5_theorem_gated
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact False.elim (hno ⟨s⟩)

/--
Prime-3 interpolation from the same sharper pair-{2,5} theorem surface.
-/
theorem sin_log3_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
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
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_pair25_sigma2delta_bCoeff5_theorem_gated
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res)
  exact False.elim (hno ⟨s⟩)

/--
Final-local-scalar-target Xi-side closure from the sharper pair-{2,5}
sigma2/bCoeff5 surface.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_from_pair25_sigma2delta_bCoeff5
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
  exact noOffSeed_Xi_of_final_local_scalar_target
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res))

theorem noOffSeed_Zeta_of_final_local_scalar_target_from_pair25_sigma2delta_bCoeff5
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
  exact noOffSeed_Zeta_of_final_local_scalar_target
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res))

theorem criticalzero_zeta_of_final_local_scalar_target_from_pair25_sigma2delta_bCoeff5
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
  exact criticalzero_zeta_of_final_local_scalar_target
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Prime-3 twin from the sharper pair-{2,5} sigma2/bCoeff5 surface.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_prime3_from_pair25_sigma2delta_bCoeff5
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
  exact noOffSeed_Xi_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res))

theorem noOffSeed_Zeta_of_final_local_scalar_target_prime3_from_pair25_sigma2delta_bCoeff5
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
  exact noOffSeed_Zeta_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res))

theorem criticalzero_zeta_of_final_local_scalar_target_prime3_from_pair25_sigma2delta_bCoeff5
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
  exact criticalzero_zeta_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res := hσ2δ_res)
      (hb5_res := hb5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
