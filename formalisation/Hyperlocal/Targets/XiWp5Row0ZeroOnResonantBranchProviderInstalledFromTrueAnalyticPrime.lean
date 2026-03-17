import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_GenericPrime
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Exact wp5 resonant-branch theorem discharged from the genuine global
generic-prime true-analytic producer.

The resonant hypothesis is unused here: the generic-prime row-0 zero for
`wpAt 0 s 5` is already global.
-/
theorem wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  intro s _hres
  rw [← toeplitzL_row0_eq_row0Sigma (s := s) (w := wpAt 0 s 5)]
  exact xiJetQuot_row0_wpAt_of_trueAnalyticPrime (m := 0) (s := s) (p := 5)

/--
Installed wp5 resonant-branch provider from the global generic-prime
true-analytic producer.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderInstalledFromTrueAnalyticPrime
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    XiWp5Row0ZeroOnResonantBranchProvider where
  wp5_row0_zero_on_resonant_branch :=
    wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime

#print axioms wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime

end Targets
end Hyperlocal
