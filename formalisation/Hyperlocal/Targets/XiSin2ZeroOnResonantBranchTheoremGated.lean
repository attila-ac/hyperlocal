import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranch
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
Honest prime-2 resonant sine theorem surface.

This is not closed. It exposes the exact hidden pair-{2,5} corridor currently
required by `noOffSeed_Xi_via_pair25_resonant_branch`.
-/
theorem sin2_zero_on_resonant_branch_pair25_corridor
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi := by
    exact Hyperlocal.Targets.noOffSeed_Xi_via_pair25_resonant_branch
  exact False.elim (hno ⟨s⟩)

#print axioms sin2_zero_on_resonant_branch_pair25_corridor

end Targets
end Hyperlocal
