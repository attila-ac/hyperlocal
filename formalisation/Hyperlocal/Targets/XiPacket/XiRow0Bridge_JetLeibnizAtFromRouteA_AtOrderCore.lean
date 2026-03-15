import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotFromRouteAJetEq
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

namespace JetQuotOpClean

/--
Route-A jet package specialised to the canonical jet window of the chosen `routeA_G s`.
This is a clean alternate producer surface and intentionally avoids the historical names
already occupied by the mixed wrapper.
-/
theorem xiRouteA_jetPkg_jet3_clean (s : OffSeed Xi) (z : ℂ) :
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

private theorem z_w0At_eq_rho_clean (s : OffSeed Xi) : TAC.z_w0At s = s.ρ := by
  apply Complex.ext
  · simp [TAC.z_w0At, sc, t, Hyperlocal.Targets.XiTransport.delta]
  · simp [TAC.z_w0At, sc, t, Hyperlocal.Targets.XiTransport.delta]

/--
Clean AtOrder package for `w0At`, assuming the theorem-side quotient-equality surface.
-/
theorem xiRouteA_jetPkg_w0At_clean
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (s.ρ) (w0At m s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  haveI : TAC.XiJetWindowIsJetAtOrderQuotProvider := inferInstance
  have H := xiRouteA_jetPkg_jet3_clean (s := s) (z := s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  have hq : IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) :=
    TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_w0At (m := m) (s := s)
  have hw : w0At m s = TAC.jet3 (routeA_G s) (TAC.z_w0At s) := by
    exact TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := TAC.z_w0At s) (w := w0At m s) hq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  have hjet0 : IsJet3At (routeA_G s) (TAC.z_w0At s) (TAC.jet3 (routeA_G s) (TAC.z_w0At s)) := by
    simpa using isJet3At_jet3 (routeA_G s) (TAC.z_w0At s)
  simpa [z_w0At_eq_rho_clean (s := s), hw] using hjet0

/--
Clean AtOrder package for `wp2At`, assuming the theorem-side quotient-equality surface.
-/
theorem xiRouteA_jetPkg_wp2At_clean
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G ((starRingEnd ℂ) s.ρ) (wp2At m s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  haveI : TAC.XiJetWindowIsJetAtOrderQuotProvider := inferInstance
  have H := xiRouteA_jetPkg_jet3_clean (s := s) (z := (starRingEnd ℂ) s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  have hq : IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) :=
    TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp2At (m := m) (s := s)
  have hw : wp2At m s = TAC.jet3 (routeA_G s) (TAC.z_wp2At s) := by
    exact TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := TAC.z_wp2At s) (w := wp2At m s) hq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  have hjet0 : IsJet3At (routeA_G s) (TAC.z_wp2At s) (TAC.jet3 (routeA_G s) (TAC.z_wp2At s)) := by
    simpa using isJet3At_jet3 (routeA_G s) (TAC.z_wp2At s)
  simpa [TAC.z_wp2At, hw] using hjet0

/--
Clean AtOrder package for `wp3At`, assuming the theorem-side quotient-equality surface.
-/
theorem xiRouteA_jetPkg_wp3At_clean
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  haveI : TAC.XiJetWindowIsJetAtOrderQuotProvider := inferInstance
  have H := xiRouteA_jetPkg_jet3_clean (s := s) (z := 1 - (starRingEnd ℂ) s.ρ)
  rcases H with ⟨hfac, hjet, hR, hG, hR', hG'⟩
  have hq : IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) :=
    TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp3At (m := m) (s := s)
  have hw : wp3At m s = TAC.jet3 (routeA_G s) (TAC.z_wp3At s) := by
    exact TAC.window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := TAC.z_wp3At s) (w := wp3At m s) hq
  refine ⟨routeA_G s, hfac, ?_, hR, hG, hR', hG'⟩
  have hjet0 : IsJet3At (routeA_G s) (TAC.z_wp3At s) (TAC.jet3 (routeA_G s) (TAC.z_wp3At s)) := by
    simpa using isJet3At_jet3 (routeA_G s) (TAC.z_wp3At s)
  simpa [TAC.z_wp3At, hw] using hjet0

/-- Clean AtOrder `JetLeibnizAt` for `w0At`. -/
theorem xiJetLeibnizAt_w0At_clean
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetLeibnizAt s (s.ρ) (w0At m s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := s.ρ) (w := w0At m s)
    (xiRouteA_jetPkg_w0At_clean (m := m) (s := s))

/-- Clean AtOrder `JetLeibnizAt` for `wp2At`. -/
theorem xiJetLeibnizAt_wp2At_clean
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s)
    (xiRouteA_jetPkg_wp2At_clean (m := m) (s := s))

/-- Clean AtOrder `JetLeibnizAt` for `wp3At`. -/
theorem xiJetLeibnizAt_wp3At_clean
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s)
    (xiRouteA_jetPkg_wp3At_clean (m := m) (s := s))

end JetQuotOpClean

end XiPacket
end Targets
end Hyperlocal
