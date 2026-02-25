/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Axioms.lean

  Fallback (low-priority) axiom instance for the Q1 coordinate provider.

  IMPORTANT: This file must NOT import the main API file
  XiRow0Bridge_JetWindowEqFromRouteA.lean, otherwise we create an import cycle.

  It imports only the class definition file:
    XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
  21 scalar axioms (3 coordinates per window).
  These are the ONLY Route–A bridge axioms under the Q1 refactor.
-/

-- w0 @ ρ
axiom ax_w0_0 (s : OffSeed Xi) :
    w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ)
axiom ax_w0_1 (s : OffSeed Xi) :
    w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ)
axiom ax_w0_2 (s : OffSeed Xi) :
    w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ)

-- wc @ (1 - ρ)
axiom ax_wc_0 (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ)
axiom ax_wc_1 (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ)
axiom ax_wc_2 (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ)

-- wp2 @ conj ρ
axiom ax_wp2_0 (s : OffSeed Xi) :
    wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ)
axiom ax_wp2_1 (s : OffSeed Xi) :
    wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ)
axiom ax_wp2_2 (s : OffSeed Xi) :
    wp2 s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ)

-- wp3 @ (1 - conj ρ)
axiom ax_wp3_0 (s : OffSeed Xi) :
    wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
axiom ax_wp3_1 (s : OffSeed Xi) :
    wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
axiom ax_wp3_2 (s : OffSeed Xi) :
    wp3 s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ)

-- w0At @ ρ
axiom ax_w0At_0 (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ)
axiom ax_w0At_1 (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ)
axiom ax_w0At_2 (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ)

-- wp2At @ conj ρ
axiom ax_wp2At_0 (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ)
axiom ax_wp2At_1 (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ)
axiom ax_wp2At_2 (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ)

-- wp3At @ (1 - conj ρ)
axiom ax_wp3At_0 (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
axiom ax_wp3At_1 (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)
axiom ax_wp3At_2 (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ)

/--
Low-priority default provider built from axioms.
A discharge provider should be installed at higher priority.
-/
instance (priority := 10) : RouteAJetCoordProvider :=
{ w0_0 := ax_w0_0, w0_1 := ax_w0_1, w0_2 := ax_w0_2
  wc_0 := ax_wc_0, wc_1 := ax_wc_1, wc_2 := ax_wc_2
  wp2_0 := ax_wp2_0, wp2_1 := ax_wp2_1, wp2_2 := ax_wp2_2
  wp3_0 := ax_wp3_0, wp3_1 := ax_wp3_1, wp3_2 := ax_wp3_2
  w0At_0 := ax_w0At_0, w0At_1 := ax_w0At_1, w0At_2 := ax_w0At_2
  wp2At_0 := ax_wp2At_0, wp2At_1 := ax_wp2At_1, wp2At_2 := ax_wp2At_2
  wp3At_0 := ax_wp3At_0, wp3At_1 := ax_wp3At_1, wp3At_2 := ax_wp3At_2 }

end XiPacket
end Targets
end Hyperlocal
