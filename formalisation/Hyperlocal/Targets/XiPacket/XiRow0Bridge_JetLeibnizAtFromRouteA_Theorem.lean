/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem.lean

  Theorem-side Route-A JetLeibniz surface.

  IMPORTANT:
  * no legacy mixed wrapper import
  * true prerequisite stated explicitly:
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

private theorem z_w0At_eq_rho (s : OffSeed Xi) : TAC.z_w0At s = s.ρ := by
  apply Complex.ext <;>
    simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]

namespace JetQuotOpTheorem

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

theorem xiRouteA_jetPkg_w0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
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
  have hw0 : w0 s = jet3 (routeA_G s) (s.ρ) := by
    simpa [w0At_zero, TAC.jet3, z_w0At_eq_rho (s := s)] using
      (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).w0At_eq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  rw [hw0]
  exact hjet

theorem xiRouteA_jetPkg_wc
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (1 - s.ρ) (wc s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  have H := xiRouteA_jetPkg_jet3 (s := s) (z := 1 - s.ρ)
  rcases H with ⟨hfac, _, hR, hG, hR', hG'⟩
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  exact JetQuotOp.wc_isJet3At_routeA (s := s)

theorem xiRouteA_jetPkg_wp2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
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
  have hwp2 : wp2 s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) := by
    simpa [wp2At_zero, TAC.z_wp2At] using
      (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp2At_eq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  rw [hwp2]
  exact hjet

theorem xiRouteA_jetPkg_wp3
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
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
  have hwp3 : wp3 s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) := by
    simpa [wp3At_zero, TAC.z_wp3At] using
      (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp3At_eq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  rw [hwp3]
  exact hjet

theorem xiRouteA_jetPkg_w0At
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
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
  have hw0 : w0At m s = jet3 (routeA_G s) (s.ρ) := by
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using
      (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).w0At_eq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  rw [hw0]
  exact hjet

theorem xiRouteA_jetPkg_wp2At
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
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
  have hwp2 : wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ) := by
    simpa [TAC.z_wp2At] using
      (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp2At_eq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  rw [hwp2]
  exact hjet

theorem xiRouteA_jetPkg_wp3At
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
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
  have hwp3 : wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) := by
    simpa [TAC.z_wp3At] using
      (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp3At_eq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  rw [hwp3]
  exact hjet

theorem xiJetLeibnizAt_w0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetLeibnizAt s (s.ρ) (w0 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := s.ρ) (w := w0 s)
    (xiRouteA_jetPkg_w0 (s := s))

theorem xiJetLeibnizAt_wc
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    JetLeibnizAt s (1 - s.ρ) (wc s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - s.ρ) (w := wc s)
    (xiRouteA_jetPkg_wc (s := s))

theorem xiJetLeibnizAt_wp2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (xiRouteA_jetPkg_wp2 (s := s))

theorem xiJetLeibnizAt_wp3
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3 s)
    (xiRouteA_jetPkg_wp3 (s := s))

end JetQuotOpTheorem

end XiPacket
end Targets
end Hyperlocal
