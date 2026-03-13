/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderDraft.lean

  Draft audit surface for the upstream `wc` Route-A jet theorem.

  IMPORTANT (2026-03-13):
  * this theorem now depends only on `[RouteAWcScalarProvider]`
  * therefore the theorem constant itself no longer hardwires the residual
    `base` fallback
  * the fallback remains only in the low-priority scalar-provider installer
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderFromScalars
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace JetQuotOp

theorem wc_isJet3At_routeA_draft
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  exact wc_isJet3At_routeA (s := s)

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
