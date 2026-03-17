import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Exact remaining local theorem surface for the pair-{2,5} endgame.

This is the honest single producer still missing for the final no-binder closure:
on the exact `log(3/2)` resonant branch, the row-0 `wpAt ... 5` scalar vanishes.
-/
class XiWp5Row0ZeroOnResonantBranchProvider : Prop where
  wp5_row0_zero_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0

/--
Consumer wrapper for the exact remaining local theorem surface.
-/
theorem wp5_row0_zero_on_resonant_branch_provided
    [XiWp5Row0ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 :=
  XiWp5Row0ZeroOnResonantBranchProvider.wp5_row0_zero_on_resonant_branch

end Targets
end Hyperlocal
