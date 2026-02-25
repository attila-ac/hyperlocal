/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA.lean

  Q1 refactor (2026-02-24+):

  Main API file: NO axioms here.

  We expose:
    • a typeclass `RouteAJetCoordProvider` packaging the 21 scalar coordinate facts
    • projection lemmas with the old names `w0_coord0_routeA`, ... (for compatibility)
    • theorem-level window = jet3 lemmas `w0_eq_jet3_routeA`, ... built from the 3 coords

  Default behavior remains green because we import the fallback axiom instance
  from `..._Axioms.lean` (low priority). If a discharge instance is available,
  it can override the axiom instance by higher priority.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Axioms
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
  ## Backwards-compatible projection lemmas (same names as before)
-/

section Projections
variable [RouteAJetCoordProvider]

-- w0
lemma w0_coord0_routeA (s : OffSeed Xi) :
    w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) :=
  RouteAJetCoordProvider.w0_0 (s := s)

lemma w0_coord1_routeA (s : OffSeed Xi) :
    w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ) :=
  RouteAJetCoordProvider.w0_1 (s := s)

lemma w0_coord2_routeA (s : OffSeed Xi) :
    w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ) :=
  RouteAJetCoordProvider.w0_2 (s := s)

-- wc
lemma wc_coord0_routeA (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) :=
  RouteAJetCoordProvider.wc_0 (s := s)

lemma wc_coord1_routeA (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) :=
  RouteAJetCoordProvider.wc_1 (s := s)

lemma wc_coord2_routeA (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) :=
  RouteAJetCoordProvider.wc_2 (s := s)

-- wp2
lemma wp2_coord0_routeA (s : OffSeed Xi) :
    wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp2_0 (s := s)

lemma wp2_coord1_routeA (s : OffSeed Xi) :
    wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp2_1 (s := s)

lemma wp2_coord2_routeA (s : OffSeed Xi) :
    wp2 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp2_2 (s := s)

-- wp3
lemma wp3_coord0_routeA (s : OffSeed Xi) :
    wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp3_0 (s := s)

lemma wp3_coord1_routeA (s : OffSeed Xi) :
    wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp3_1 (s := s)

lemma wp3_coord2_routeA (s : OffSeed Xi) :
    wp3 s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp3_2 (s := s)

-- w0At
lemma w0At_coord0_routeA (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ) :=
  RouteAJetCoordProvider.w0At_0 (m := m) (s := s)

lemma w0At_coord1_routeA (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ) :=
  RouteAJetCoordProvider.w0At_1 (m := m) (s := s)

lemma w0At_coord2_routeA (m : ℕ) (s : OffSeed Xi) :
    w0At m s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ) :=
  RouteAJetCoordProvider.w0At_2 (m := m) (s := s)

-- wp2At
lemma wp2At_coord0_routeA (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp2At_0 (m := m) (s := s)

lemma wp2At_coord1_routeA (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp2At_1 (m := m) (s := s)

lemma wp2At_coord2_routeA (m : ℕ) (s : OffSeed Xi) :
    wp2At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp2At_2 (m := m) (s := s)

-- wp3At
lemma wp3At_coord0_routeA (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp3At_0 (m := m) (s := s)

lemma wp3At_coord1_routeA (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp3At_1 (m := m) (s := s)

lemma wp3At_coord2_routeA (m : ℕ) (s : OffSeed Xi) :
    wp3At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) :=
  RouteAJetCoordProvider.wp3At_2 (m := m) (s := s)

end Projections

/-!
  ## Theorem-level window = jet3 consequences (Q1 outcome)
-/

/-- Generic 3-coordinate reduction. -/
theorem window_eq_jet3_of_coords
    (G : ℂ → ℂ) (z : ℂ) (w : Window 3)
    (h0 : w ⟨0, by decide⟩ = G z)
    (h1 : w ⟨1, by decide⟩ = deriv G z)
    (h2 : w ⟨2, by decide⟩ = deriv (deriv G) z) :
    w = jet3 G z := by
  have h0' : w (0 : Fin 3) = G z := by simpa using h0
  have h1' : w (1 : Fin 3) = deriv G z := by simpa using h1
  have h2' : w (2 : Fin 3) = deriv (deriv G) z := by simpa using h2
  ext i
  fin_cases i <;> simp [h0', h1', h2']

section WindowEq
variable [RouteAJetCoordProvider]

theorem w0_eq_jet3_routeA (s : OffSeed Xi) :
    w0 s = jet3 (routeA_G s) (s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := s.ρ) (w := w0 s)
    (w0_coord0_routeA (s := s))
    (w0_coord1_routeA (s := s))
    (w0_coord2_routeA (s := s))

theorem wc_eq_jet3_routeA (s : OffSeed Xi) :
    wc s = jet3 (routeA_G s) (1 - s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (1 - s.ρ)) (w := wc s)
    (wc_coord0_routeA (s := s))
    (wc_coord1_routeA (s := s))
    (wc_coord2_routeA (s := s))

theorem wp2_eq_jet3_routeA (s : OffSeed Xi) :
    wp2 s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (wp2_coord0_routeA (s := s))
    (wp2_coord1_routeA (s := s))
    (wp2_coord2_routeA (s := s))

theorem wp3_eq_jet3_routeA (s : OffSeed Xi) :
    wp3 s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s)
    (wp3_coord0_routeA (s := s))
    (wp3_coord1_routeA (s := s))
    (wp3_coord2_routeA (s := s))

theorem w0At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    w0At m s = jet3 (routeA_G s) (s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := s.ρ) (w := w0At m s)
    (w0At_coord0_routeA (m := m) (s := s))
    (w0At_coord1_routeA (m := m) (s := s))
    (w0At_coord2_routeA (m := m) (s := s))

theorem wp2At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s)
    (wp2At_coord0_routeA (m := m) (s := s))
    (wp2At_coord1_routeA (m := m) (s := s))
    (wp2At_coord2_routeA (m := m) (s := s))

theorem wp3At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s)
    (wp3At_coord0_routeA (m := m) (s := s))
    (wp3At_coord1_routeA (m := m) (s := s))
    (wp3At_coord2_routeA (m := m) (s := s))

end WindowEq

end XiPacket
end Targets
end Hyperlocal
