/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Axioms.lean

  Fallback (low-priority) axiom instance for the Q1 coordinate provider.

  AXIOM COMPRESSION (2026-02-28):
  Replace 21 separate axiom declarations by ONE bundled axiom
  `routeAJetCoordProvider_axiom : RouteAJetCoordProvider`, then re-export the
  legacy names as theorem projections.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Single bundled axiom providing the full Route–A coordinate provider. -/
axiom routeAJetCoordProvider_axiom : RouteAJetCoordProvider

/-- Low-priority fallback instance. -/
instance (priority := 10) : RouteAJetCoordProvider :=
  routeAJetCoordProvider_axiom

/-!
Back-compat: keep the old `ax_*` names, but they are *theorems* now (projections),
not additional axioms.
-/
namespace RouteAJetCoordAxioms

theorem ax_w0_0 (s : OffSeed Xi) :
    w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) :=
  (routeAJetCoordProvider_axiom).w0_0 s

theorem ax_w0_1 (s : OffSeed Xi) :
    w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ) :=
  (routeAJetCoordProvider_axiom).w0_1 s

theorem ax_w0_2 (s : OffSeed Xi) :
    w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ) :=
  (routeAJetCoordProvider_axiom).w0_2 s

theorem ax_wc_0 (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) :=
  (routeAJetCoordProvider_axiom).wc_0 s

theorem ax_wc_1 (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) :=
  (routeAJetCoordProvider_axiom).wc_1 s

theorem ax_wc_2 (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) :=
  (routeAJetCoordProvider_axiom).wc_2 s

theorem ax_wp2_0 (s : OffSeed Xi) :
    wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp2_0 s

theorem ax_wp2_1 (s : OffSeed Xi) :
    wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp2_1 s

theorem ax_wp2_2 (s : OffSeed Xi) :
    wp2 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp2_2 s

theorem ax_wp3_0 (s : OffSeed Xi) :
    wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp3_0 s

theorem ax_wp3_1 (s : OffSeed Xi) :
    wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp3_1 s

theorem ax_wp3_2 (s : OffSeed Xi) :
    wp3 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp3_2 s

theorem ax_w0At_0 (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) :=
  (routeAJetCoordProvider_axiom).w0At_0 m s

theorem ax_w0At_1 (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨1, by decide⟩ = cderivIter 1 (routeA_G s) (s.ρ) :=
  (routeAJetCoordProvider_axiom).w0At_1 m s

theorem ax_w0At_2 (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨2, by decide⟩ = cderivIter 2 (routeA_G s) (s.ρ) :=
  (routeAJetCoordProvider_axiom).w0At_2 m s

theorem ax_wp2At_0 (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp2At_0 m s

theorem ax_wp2At_1 (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨1, by decide⟩ = cderivIter 1 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp2At_1 m s

theorem ax_wp2At_2 (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨2, by decide⟩ = cderivIter 2 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp2At_2 m s

theorem ax_wp3At_0 (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp3At_0 m s

theorem ax_wp3At_1 (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨1, by decide⟩ = cderivIter 1 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp3At_1 m s

theorem ax_wp3At_2 (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨2, by decide⟩ = cderivIter 2 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  (routeAJetCoordProvider_axiom).wp3At_2 m s

end RouteAJetCoordAxioms

end XiPacket
end Targets
end Hyperlocal
