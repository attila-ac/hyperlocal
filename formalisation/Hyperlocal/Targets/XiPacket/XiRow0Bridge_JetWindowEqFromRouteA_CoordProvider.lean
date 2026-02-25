/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider.lean

  Q1: the discharge surface packaged as a single typeclass.

  This file is intentionally tiny and cycle-safe:
  it defines ONLY the class `RouteAJetCoordProvider`.

  Both:
    • XiRow0Bridge_JetWindowEqFromRouteA.lean
    • XiRow0Bridge_JetWindowEqFromRouteA_Axioms.lean
  import this file, avoiding circular imports.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Route–A coordinate equalities for each consumer window and each coordinate 0/1/2.

This is the ONLY interface the rest of the system should depend on for Q1.
-/
class RouteAJetCoordProvider : Prop :=
  -- w0 @ ρ
  (w0_0 : ∀ s : OffSeed Xi, w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ))
  (w0_1 : ∀ s : OffSeed Xi, w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ))
  (w0_2 : ∀ s : OffSeed Xi, w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ))

  -- wc @ (1 - ρ)
  (wc_0 : ∀ s : OffSeed Xi, wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ))
  (wc_1 : ∀ s : OffSeed Xi, wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ))
  (wc_2 : ∀ s : OffSeed Xi, wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ))

  -- wp2 @ conj ρ
  (wp2_0 : ∀ s : OffSeed Xi, wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ))
  (wp2_1 : ∀ s : OffSeed Xi, wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ))
  (wp2_2 : ∀ s : OffSeed Xi, wp2 s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ))

  -- wp3 @ (1 - conj ρ)
  (wp3_0 : ∀ s : OffSeed Xi, wp3 s ⟨0, by decide⟩ =
      (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
  (wp3_1 : ∀ s : OffSeed Xi, wp3 s ⟨1, by decide⟩ =
      deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
  (wp3_2 : ∀ s : OffSeed Xi, wp3 s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ))

  -- w0At @ ρ
  (w0At_0 : ∀ m : ℕ, ∀ s : OffSeed Xi, w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ))
  (w0At_1 : ∀ m : ℕ, ∀ s : OffSeed Xi, w0At m s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ))
  (w0At_2 : ∀ m : ℕ, ∀ s : OffSeed Xi, w0At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (s.ρ))

  -- wp2At @ conj ρ
  (wp2At_0 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp2At m s ⟨0, by decide⟩ =
      (routeA_G s) ((starRingEnd ℂ) s.ρ))
  (wp2At_1 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp2At m s ⟨1, by decide⟩ =
      deriv (routeA_G s) ((starRingEnd ℂ) s.ρ))
  (wp2At_2 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp2At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ))

  -- wp3At @ (1 - conj ρ)
  (wp3At_0 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp3At m s ⟨0, by decide⟩ =
      (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
  (wp3At_1 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp3At m s ⟨1, by decide⟩ =
      deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
  (wp3At_2 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp3At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ))

end XiPacket
end Targets
end Hyperlocal
