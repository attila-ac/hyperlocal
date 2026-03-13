/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcCoordsFromRouteAJetLeibniz.lean

  Upstream theorem-side `wc` coordinate facts from the Route-A jet equality.

  IMPORTANT (2026-03-13):
  * this file is independent of `...WcJetProviderFromScalars`
  * it works from the axiom-free Route-A window=jet3 core
  * the honest prerequisite is `[RouteAJetCoordProvider]`
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Core
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

variable [RouteAJetCoordProvider]

namespace JetQuotOp

private lemma isJet3At_wc_routeA (s : OffSeed Xi) :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  simpa [wc_eq_jet3_routeA (s := s)] using
    (isJet3At_jet3 (routeA_G s) (1 - s.ρ))

lemma wc_0_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.1

lemma wc_1_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.2.1

lemma wc_2_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.2.2

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
