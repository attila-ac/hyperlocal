import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Hyperlocal.Targets.XiSin2ProviderFromEquivalentResonantBranchSeams
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket

/--
Installed final RH corridor provider from resonant-branch equivalent local form (A):
`row0Sigma s (wc s) = 0`.

This is the highest-leverage provider promotion on the current graph:
once the theorem-side trio and the resonant-branch wc-row0 seam are installed,
Lean 155 already yields `sin2`, hence the standard bridge yields `wp5`, hence the
bundled final corridor is automatic.
-/
instance instXiFinalRhCorridorProviderOfRow0SigmaWcZeroOnResonantBranch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiRow0SigmaWcZeroOnResonantBranchProvider] :
    XiFinalRhCorridorProvider := by
  infer_instance

/--
Installed final RH corridor provider from resonant-branch equivalent local form (C):
`σ2 = 2 * delta`.

Again, Lean 155 already promotes this seam to the prime-2 sine provider, from
which the standard `wp5` provider and then the bundled final corridor follow.
-/
instance instXiFinalRhCorridorProviderOfSigma2EqTwoDeltaOnResonantBranch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider] :
    XiFinalRhCorridorProvider := by
  infer_instance

end Targets
end Hyperlocal
