/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcCoordsFromRouteAJetLeibniz.lean

  E1 completion helper:
  discharge the three coordinate equalities for the definitional window `wc s`
  for the *chosen* Route–A witness `routeA_G s`, without using any coord-provider axioms.

  Key trick:
  use the non-existential package
      JetQuotOp.xiRouteA_jetPkg_jet3 (s := s) (z := 1 - s.ρ)
  which contains
      IsJet3At (routeA_G s) (1 - s.ρ) (jet3 (routeA_G s) (1 - s.ρ)),
  then rewrite `jet3 ...` to `wc s` via `wc_eq_jet3_routeA`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace JetQuotOp

/-- The `IsJet3At` payload for `wc s` at `z = 1 - s.ρ`, for the chosen `routeA_G s`. -/
private lemma isJet3At_wc_routeA (s : OffSeed Xi) :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := (1 - s.ρ))
  -- H : hfac ∧ hjet ∧ hR ∧ hG ∧ hR' ∧ hG'
  have hjet :
      IsJet3At (routeA_G s) (1 - s.ρ) (jet3 (routeA_G s) (1 - s.ρ)) :=
    H.2.1
  -- rewrite the canonical jet window to the concrete window `wc s`
  simpa [wc_eq_jet3_routeA (s := s)] using hjet

/-- Coordinate 0 for `wc`. -/
lemma wc_0_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.1

/-- Coordinate 1 for `wc`. -/
lemma wc_1_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.2.1

/-- Coordinate 2 for `wc`. -/
lemma wc_2_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.2.2

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
