import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderBridges
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Installed prime-2 resonant sine provider from an explicit theorem input.

This packages the remaining one-prime local theorem seam
  sin(t(s) * log(3/2)) = 0 -> sin(t(s) * log 2) = 0
into the standard provider class.
-/
instance instXiSin2ZeroOnResonantBranchProviderInstalled
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    XiSin2ZeroOnResonantBranchProvider where
  sin2_zero_on_resonant_branch := h2_res

end Targets
end Hyperlocal
