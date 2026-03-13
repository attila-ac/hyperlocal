/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Axioms.lean

  Historical compatibility surface for the full Route-A coordinate provider.

  IMPORTANT (2026-03-13):
  * this file is no longer an axiom boundary
  * keep the old theorem names `ax_*` for compatibility
  * re-export them from the live theorem-side coord-provider surface
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace RouteAJetCoordAxioms

theorem ax_w0_0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).w0_0 s

theorem ax_w0_1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).w0_1 s

theorem ax_w0_2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).w0_2 s

theorem ax_wc_0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wc_0 s

theorem ax_wc_1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wc_1 s

theorem ax_wc_2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wc_2 s

theorem ax_wp2_0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp2_0 s

theorem ax_wp2_1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp2_1 s

theorem ax_wp2_2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp2 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp2_2 s

theorem ax_wp3_0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp3_0 s

theorem ax_wp3_1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp3_1 s

theorem ax_wp3_2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp3 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp3_2 s

theorem ax_w0At_0
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).w0At_0 m s

theorem ax_w0At_1
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    w0At m s ⟨1, by decide⟩ = cderivIter 1 (routeA_G s) (s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).w0At_1 m s

theorem ax_w0At_2
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    w0At m s ⟨2, by decide⟩ = cderivIter 2 (routeA_G s) (s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).w0At_2 m s

theorem ax_wp2At_0
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp2At m s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp2At_0 m s

theorem ax_wp2At_1
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp2At m s ⟨1, by decide⟩ = cderivIter 1 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp2At_1 m s

theorem ax_wp2At_2
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp2At m s ⟨2, by decide⟩ = cderivIter 2 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp2At_2 m s

theorem ax_wp3At_0
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp3At m s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp3At_0 m s

theorem ax_wp3At_1
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp3At m s ⟨1, by decide⟩ = cderivIter 1 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp3At_1 m s

theorem ax_wp3At_2
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    wp3At m s ⟨2, by decide⟩ = cderivIter 2 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (inferInstance : RouteAJetCoordProvider).wp3At_2 m s

end RouteAJetCoordAxioms

end XiPacket
end Targets
end Hyperlocal
