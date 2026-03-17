import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Installed exact wp5 resonant-branch provider from an explicit theorem input.

This packages the single remaining local theorem gate
  row0Sigma s (wpAt 0 s 5) = 0
on the exact `log(3/2)` resonant branch into the standard provider class.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderInstalled
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    XiWp5Row0ZeroOnResonantBranchProvider where
  wp5_row0_zero_on_resonant_branch := hwp5_res

end Targets
end Hyperlocal
