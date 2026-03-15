/-
  Hyperlocal/Targets/XiNoOffSeedDirectFromPair25ResonantBranch.lean

  Final pair-switch closure candidate:

  * the first pair `{2,3}` already kills the nonresonant branch;
  * the second pair `{2,5}` kills the exact resonant branch of `{2,3}`
    by forcing

        row0Sigma s (wc s) = 0

    on that branch;
  * the existing resonant-branch seam reducer then closes the Xi / zeta / RH
    endpoint.

  This is the clean top-level consumer of the new pair-`{2,5}` theorem.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Hyperlocal.Targets.XiNoOffSeedDirectFromResonantBranchSeams
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

/--
Xi-side closure via the second finite pair `{2,5}` on the exact resonant branch.
-/
theorem noOffSeed_Xi_via_pair25_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch
    (hsigma_res := fun s hres =>
      Hyperlocal.Targets.XiPacket.W1.row0Sigma_wc_eq_zero_of_resonant32
        (s := s) (hres := hres))

/--
ζ-side closure via the second finite pair `{2,5}`.
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
RH-facing export via the second finite pair `{2,5}`.
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
