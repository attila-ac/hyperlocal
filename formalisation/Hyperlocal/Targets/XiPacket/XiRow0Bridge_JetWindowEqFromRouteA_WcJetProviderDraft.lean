/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderDraft.lean

  Draft theorem-side installer for the upstream `wc` jet provider.

  IMPORTANT (2026-03-13):
  * the original draft `sorry` has now been replaced by the live theorem-side
    scalar Route-A bridge from `...WcJetProviderFromScalars`
  * this file remains a draft / audit surface so the upstream target is still
    visible under the explicit name `wc_isJet3At_routeA_draft`
  * this does NOT yet make the proof independent of the residual `base` axiom;
    it only synchronizes the draft milestone with the current live theorem lane
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProvider
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

/--
Draft upstream theorem for the `wc` Route-A jet fact.

At the current milestone this is discharged by the live theorem-side scalar
Route-A bridge. The remaining \emph{real} upstream task is still to replace
that scalar route by a proof independent of the residual `base` fallback.
-/
theorem wc_isJet3At_routeA_draft
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  exact wc_isJet3At_routeA (s := s)

end JetQuotOp

/--
Draft theorem-side installer for the upstream `wc` jet provider.
-/
instance (priority := 1000)
    [TAC.XiJetWindowEqAtOrderQuotProvider] : RouteAWcJetProvider where
  jet_wc := by
    intro s
    exact JetQuotOp.wc_isJet3At_routeA_draft (s := s)

end XiPacket
end Targets
end Hyperlocal
