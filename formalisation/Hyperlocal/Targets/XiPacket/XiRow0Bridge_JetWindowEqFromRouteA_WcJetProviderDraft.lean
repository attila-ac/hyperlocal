/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderDraft.lean

  First-draft theorem-side installer for the upstream `wc` jet provider.

  IMPORTANT:
  * this file is intentionally a draft
  * it uses `sorry`, not the historical `Wc` axiom payload
  * the proof hole is the *real remaining theorem task*:
      prove `wc s` is the Route-A jet at `1 - s.ρ`
    without going through `wc_eq_jet3_routeA`
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetPkgFromAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
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
Draft upstream theorem for the missing `wc` Route-A jet fact.

Intended proof route:
1. obtain the theorem-side analytic quotient jet package at `z = 1 - s.ρ`
   from `xiRouteA_jetPkg_jet3`;
2. identify the chosen quotient with `routeA_G s` on the canonical Route-A surface;
3. prove that the definitional window `wc s` is the same jet window, *without*
   using `wc_eq_jet3_routeA`.

This is the real frontier seam. The `sorry` is deliberate and replaces the
historical axiom edge with an explicit theorem hole.
-/
theorem wc_isJet3At_routeA_draft
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  classical

  -- Clean upstream analytic package at the canonical jet window.
  have H := JetQuotOp.xiRouteA_jetPkg_jet3 (s := s) (z := (1 - s.ρ))
  rcases H with ⟨G, hfac, hjet, hR, hG, hR', hG'⟩

  /-
    TODO frontier seam:

    We now need an *upstream* bridge from the canonical theorem-side quotient `G`
    and its raw jet window `jet3 G (1 - s.ρ)` to the concrete definitional window `wc s`,
    specialized to the Route-A quotient.

    Concretely, one clean completion route would be:
      * prove/obtain `G = routeA_G s`,
      * prove/obtain `wc s = jet3 (routeA_G s) (1 - s.ρ)`,
        but NOT via the downstream lemma `wc_eq_jet3_routeA`.

    At that point `simpa` finishes.
  -/
  sorry

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
