/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
  ### Coordinatewise reduction lemmas (theorem-level, no axioms)
-/

/-- Generic 3-coordinate reduction: prove `w = jet3 G z` from scalar coordinate equalities. -/
theorem window_eq_jet3_of_coords
    (G : ℂ → ℂ) (z : ℂ) (w : Window 3)
    (h0 : w ⟨0, by decide⟩ = G z)
    (h1 : w ⟨1, by decide⟩ = deriv G z)
    (h2 : w ⟨2, by decide⟩ = deriv (deriv G) z) :
    w = jet3 G z := by
  -- normalize hypotheses to numeral indices (0/1/2 : Fin 3)
  have h0' : w (0 : Fin 3) = G z := by simpa using h0
  have h1' : w (1 : Fin 3) = deriv G z := by simpa using h1
  have h2' : w (2 : Fin 3) = deriv (deriv G) z := by simpa using h2
  ext i
  fin_cases i <;> simp [h0', h1', h2']

/-- Specialized reducers. -/
theorem w0_eq_jet3_routeA_of_coords (s : OffSeed Xi)
    (h0 : w0 s ⟨0, by decide⟩ = (routeA_G s) (s.ρ))
    (h1 : w0 s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ))
    (h2 : w0 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ)) :
    w0 s = jet3 (routeA_G s) (s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := s.ρ) (w := w0 s) h0 h1 h2

theorem wc_eq_jet3_routeA_of_coords (s : OffSeed Xi)
    (h0 : wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ))
    (h1 : wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ))
    (h2 : wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ)) :
    wc s = jet3 (routeA_G s) (1 - s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (1 - s.ρ)) (w := wc s) h0 h1 h2

theorem wp2_eq_jet3_routeA_of_coords (s : OffSeed Xi)
    (h0 : wp2 s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ))
    (h1 : wp2 s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ))
    (h2 : wp2 s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ)) :
    wp2 s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s) h0 h1 h2

theorem wp3_eq_jet3_routeA_of_coords (s : OffSeed Xi)
    (h0 : wp3 s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
    (h1 : wp3 s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
    (h2 : wp3 s ⟨2, by decide⟩ =
          deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ)) :
    wp3 s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords
    (G := routeA_G s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s) h0 h1 h2

theorem w0At_eq_jet3_routeA_of_coords (m : ℕ) (s : OffSeed Xi)
    (h0 : w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ))
    (h1 : w0At m s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ))
    (h2 : w0At m s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (s.ρ)) :
    w0At m s = jet3 (routeA_G s) (s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := s.ρ) (w := w0At m s) h0 h1 h2

theorem wp2At_eq_jet3_routeA_of_coords (m : ℕ) (s : OffSeed Xi)
    (h0 : wp2At m s ⟨0, by decide⟩ = (routeA_G s) ((starRingEnd ℂ) s.ρ))
    (h1 : wp2At m s ⟨1, by decide⟩ = deriv (routeA_G s) ((starRingEnd ℂ) s.ρ))
    (h2 : wp2At m s ⟨2, by decide⟩ =
          deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ)) :
    wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords (G := routeA_G s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) h0 h1 h2

theorem wp3At_eq_jet3_routeA_of_coords (m : ℕ) (s : OffSeed Xi)
    (h0 : wp3At m s ⟨0, by decide⟩ = (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
    (h1 : wp3At m s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
    (h2 : wp3At m s ⟨2, by decide⟩ =
          deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ)) :
    wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) :=
  window_eq_jet3_of_coords
    (G := routeA_G s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) h0 h1 h2

/-!
  ### Remaining Route-A bridge obligations (still axiomatic)
-/

axiom w0_eq_jet3_routeA (s : OffSeed Xi) :
    w0 s = jet3 (routeA_G s) (s.ρ)

axiom wc_eq_jet3_routeA (s : OffSeed Xi) :
    wc s = jet3 (routeA_G s) (1 - s.ρ)

axiom wp2_eq_jet3_routeA (s : OffSeed Xi) :
    wp2 s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)

axiom wp3_eq_jet3_routeA (s : OffSeed Xi) :
    wp3 s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)

axiom w0At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    w0At m s = jet3 (routeA_G s) (s.ρ)

axiom wp2At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)

axiom wp3At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)

end XiPacket
end Targets
end Hyperlocal
