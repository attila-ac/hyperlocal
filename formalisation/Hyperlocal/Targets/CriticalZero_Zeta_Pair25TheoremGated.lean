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
Consumer-facing pair-{2,5} Xi-side closure with the theorem gates made explicit.

This is the honest current surface in the snapshot:
it is not assumption-free, because the Rec2 true-analytic and generic-prime
corridors are not globally installed at the project root.
-/
theorem noOffSeed_Xi_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  exact Hyperlocal.Targets.noOffSeed_Xi_via_pair25_resonant_branch

/--
Consumer-facing pair-{2,5} ζ-side closure with explicit theorem gates.
-/
theorem noOffSeed_Zeta_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact Hyperlocal.Targets.noOffSeed_Zeta_via_pair25_resonant_branch

/--
Consumer-facing RH-facing pair-{2,5} export with explicit theorem gates.
-/
theorem criticalzero_zeta_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact Hyperlocal.Targets.criticalzero_zeta_via_pair25_resonant_branch
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
