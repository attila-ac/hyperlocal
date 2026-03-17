import Hyperlocal.Targets.XiPair25ResonantScalarProviderInstalled
import Hyperlocal.Targets.XiPair25Sigma2TheoremSurface
import Hyperlocal.XiBCoeff5ZeroOnResonantBranchFromWp5
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Installed bundled pair-{2,5} scalar provider from the single wp5 resonant-branch
theorem surface.

This shows that once the local wp5 seam is closed, the split pair-{2,5} scalar
provider is automatic: `σ2 = 2*delta` and `bCoeff5 = 0` both follow.
-/
instance instXiPair25ResonantScalarProviderInstalledFromWp5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    XiPair25ResonantScalarProvider :=
  instXiPair25ResonantScalarProviderInstalled
    (hσ2δ_res :=
      sigma2_eq_two_delta_on_resonant_branch_of_wp5
        (hwp5_res := hwp5_res))
    (hb5_res :=
      bCoeff5_zero_on_resonant_branch_of_wp5
        (hwp5_res := hwp5_res))

end Targets
end Hyperlocal
