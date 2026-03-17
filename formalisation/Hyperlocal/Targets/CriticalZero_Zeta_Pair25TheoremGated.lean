import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranch
import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranchSigma2DeltaBCoeff5
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
Consumer-facing pair-{2,5} Xi-side closure with the honest remaining theorem
node made explicit.

The generic-prime class is no longer on the critical consumer path here.
What remains is exactly the local resonant-branch row-0 theorem at
`wpAt 0 s 5`.
-/
theorem noOffSeed_Xi_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  exact Hyperlocal.Targets.noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := hwp5_res)

/--
Consumer-facing pair-{2,5} ζ-side closure with the same explicit local theorem
burden.
-/
theorem noOffSeed_Zeta_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact Hyperlocal.Targets.noOffSeed_Zeta_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := hwp5_res)

/--
Consumer-facing RH-facing pair-{2,5} export with the sharpened local theorem
surface.
-/
theorem criticalzero_zeta_pair25_theorem_gated
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
  exact Hyperlocal.Targets.criticalzero_zeta_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := hwp5_res)
    (hζ := hζ) (hIm := hIm)

/--
Smaller pair-{2,5} theorem-gated consumer surface:
if the resonant-branch scalar facts
  σ2 = 2*delta
and
  bCoeff(...,5) = 0
are available, the pair-{2,5} route closes without the generic-prime class.
-/
theorem noOffSeed_Xi_pair25_sigma2delta_bCoeff5_theorem_gated
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
  exact
    Hyperlocal.Targets.noOffSeed_Xi_via_pair25_resonant_branch_of_sigma2_eq_two_delta_and_bCoeff5_zero
      (hσ2δ_res := hσ2δ_res) (hb5_res := hb5_res)

end Targets
end Hyperlocal
