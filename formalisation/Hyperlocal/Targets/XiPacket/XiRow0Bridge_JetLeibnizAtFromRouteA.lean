/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizAtFromRouteA.lean

  Route-A: provide JetLeibnizAt for the four canonical windows.

  Cycle safety:
  * This file must not import any Row0Semantics / Row0ConcreteProof modules.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

/-
  NOTE (2026-02-22 → next step):

  The old axiom
    `xiRouteA_jetPkg (s) (z) (w)`
  quantified over *arbitrary* windows `w`.

  We now split the problem:
  * theorem-level analytic construction/discharge at the canonical jet `jet3 G z`
    lives in `XiRow0Bridge_JetLeibnizAt_Discharge.lean`;
  * the only remaining missing link is the identification of the concrete
    ξ-windows with those canonical jets, isolated behind small axioms in
    `XiRow0Bridge_JetWindowEqFromRouteA.lean`.
-/

/-- Route-A jet package specialised to the canonical jet window of the *chosen* `routeA_G s`. -/
theorem xiRouteA_jetPkg_jet3 (s : OffSeed Xi) (z : ℂ) :
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 (routeA_G s) ∧
    IsJet3At (routeA_G s) z (jet3 (routeA_G s) z) ∧
    Differentiable ℂ (Rfun s) ∧
    Differentiable ℂ (routeA_G s) ∧
    Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
    Differentiable ℂ (fun t => deriv (routeA_G s) t) := by
  classical
  refine ⟨routeA_G_factorised s, ?_, ?_, ?_, ?_, ?_⟩
  · exact isJet3At_jet3 (routeA_G s) z
  · exact Rfun_differentiable s
  · exact G_differentiable_of_entire (routeA_G_entire s)
  · exact Rfun_deriv_differentiable s
  · exact G_deriv_differentiable_of_entire (routeA_G_entire s)

/-!
  ### Specialised Route-A packages for the concrete ξ-windows

  These replace uses of the old axiom `xiRouteA_jetPkg`.
  Each lemma is theorem-level *except* for the window=jet identification,
  which is currently provided by axioms in `XiRow0Bridge_JetWindowEqFromRouteA`.
-/

/-- Package for the definitional window `w0 s` at `z = s.ρ`. -/
theorem xiRouteA_jetPkg_w0 (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (s.ρ) (w0 s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [w0_eq_jet3_routeA (s := s)] using hjet

/-- Package for the definitional window `wc s` at `z = 1 - s.ρ`. -/
theorem xiRouteA_jetPkg_wc (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (1 - s.ρ) (wc s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := 1 - s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [wc_eq_jet3_routeA (s := s)] using hjet

/-- Package for the definitional window `wp2 s` at `z = star(s.ρ)`. -/
theorem xiRouteA_jetPkg_wp2 (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G ((starRingEnd ℂ) s.ρ) (wp2 s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := (starRingEnd ℂ) s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [wp2_eq_jet3_routeA (s := s)] using hjet

/-- Package for the definitional window `wp3 s` at `z = 1 - star(s.ρ)`. -/
theorem xiRouteA_jetPkg_wp3 (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (1 - (starRingEnd ℂ) s.ρ) (wp3 s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := 1 - (starRingEnd ℂ) s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [wp3_eq_jet3_routeA (s := s)] using hjet

/-- Package for the jet-pivot window `w0At m s` at `z = s.ρ`. -/
theorem xiRouteA_jetPkg_w0At (m : ℕ) (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (s.ρ) (w0At m s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [w0At_eq_jet3_routeA (m := m) (s := s)] using hjet

/-- Package for the jet-pivot window `wp2At m s` at `z = star(s.ρ)`. -/
theorem xiRouteA_jetPkg_wp2At (m : ℕ) (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G ((starRingEnd ℂ) s.ρ) (wp2At m s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := (starRingEnd ℂ) s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [wp2At_eq_jet3_routeA (m := m) (s := s)] using hjet

/-- Package for the jet-pivot window `wp3At m s` at `z = 1 - star(s.ρ)`. -/
theorem xiRouteA_jetPkg_wp3At (m : ℕ) (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := 1 - (starRingEnd ℂ) s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  simpa [wp3At_eq_jet3_routeA (m := m) (s := s)] using hjet

/-- `JetLeibnizAt` for the central window `w0` at `z = s.ρ`. -/
theorem xiJetLeibnizAt_w0 (s : OffSeed Xi) :
  JetLeibnizAt s (s.ρ) (w0 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := s.ρ) (w := w0 s)
    (xiRouteA_jetPkg_w0 (s := s))

/-- `JetLeibnizAt` for the conjugate window `wc` at `z = 1 - s.ρ`. -/
theorem xiJetLeibnizAt_wc (s : OffSeed Xi) :
  JetLeibnizAt s (1 - s.ρ) (wc s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - s.ρ) (w := wc s)
    (xiRouteA_jetPkg_wc (s := s))

/-- `JetLeibnizAt` for `wp2` at `z = star(s.ρ)` (as `starRingEnd`). -/
theorem xiJetLeibnizAt_wp2 (s : OffSeed Xi) :
  JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (xiRouteA_jetPkg_wp2 (s := s))

/-- `JetLeibnizAt` for `wp3` at `z = 1 - star(s.ρ)` (as `starRingEnd`). -/
theorem xiJetLeibnizAt_wp3 (s : OffSeed Xi) :
  JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3 s)
    (xiRouteA_jetPkg_wp3 (s := s))

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
