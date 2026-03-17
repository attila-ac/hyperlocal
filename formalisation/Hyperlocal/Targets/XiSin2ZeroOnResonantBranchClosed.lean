import Hyperlocal.Targets.CriticalZero_Zeta_FinalWp5ProviderGated
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
Closed no-ordinary-argument prime-2 resonant sine theorem on the exact wp5
provider surface.

This is the honest `h2_res` promotion now available after the pair-{2,5}
sharpening: once the standard theorem-side trio and the final
`wpAt 0 s 5` resonant-branch provider are installed, an off-seed on the exact
`log(3/2)` resonant branch is impossible, hence the prime-2 sine must vanish.
-/
theorem sin2_zero_on_resonant_branch_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiWp5Row0ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_final_of_wp5_resonant_branch_provider
  exact False.elim (hno ⟨s⟩)

#print axioms sin2_zero_on_resonant_branch_closed

end Targets
end Hyperlocal
