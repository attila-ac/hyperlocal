import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderBridges
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Installed resonant-branch `bCoeff(...,5)=0` provider from an explicit theorem
surface.
-/
instance instXiBCoeff5ZeroOnResonantBranchProviderInstalled
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    XiBCoeff5ZeroOnResonantBranchProvider where
  bCoeff5_zero_on_resonant_branch := hb5_res

end Targets
end Hyperlocal
