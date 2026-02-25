/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_AtCoordsFromQuotJets.lean

  True-theorem discharge for the *AtOrder* Route–A coordinate equalities (the 9 fields):
    w0At_0/1/2, wp2At_0/1/2, wp3At_0/1/2

  Source:
    [TAC.XiJetWindowIsJetAtOrderQuotProvider] (Route E quotient-jet payload)

  Snapshot quirk:
  `IsJet3At` is an And-chain, not a structure; project with `.1`, `.2.1`, `.2.2`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotFromRouteAJetEq
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Local helper: definitional alignment used in Route E: `TAC.z_w0At s = s.ρ`. -/
private theorem z_w0At_eq_rho (s : OffSeed Xi) : TAC.z_w0At s = s.ρ := by
  apply Complex.ext
  · simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]
  · simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]

/--
A smaller theorem-level interface for the 9 AtOrder coordinate equalities.
(Useful as a stepping stone towards full E1.)
-/
class RouteAJetCoordProviderAt : Prop :=
  (w0At_0 : ∀ m : ℕ, ∀ s : OffSeed Xi, w0At m s ⟨0, by decide⟩ = (routeA_G s) (s.ρ))
  (w0At_1 : ∀ m : ℕ, ∀ s : OffSeed Xi, w0At m s ⟨1, by decide⟩ = deriv (routeA_G s) (s.ρ))
  (w0At_2 : ∀ m : ℕ, ∀ s : OffSeed Xi, w0At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (s.ρ))

  (wp2At_0 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp2At m s ⟨0, by decide⟩ =
      (routeA_G s) ((starRingEnd ℂ) s.ρ))
  (wp2At_1 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp2At m s ⟨1, by decide⟩ =
      deriv (routeA_G s) ((starRingEnd ℂ) s.ρ))
  (wp2At_2 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp2At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) ((starRingEnd ℂ) s.ρ))

  (wp3At_0 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp3At m s ⟨0, by decide⟩ =
      (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
  (wp3At_1 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp3At m s ⟨1, by decide⟩ =
      deriv (routeA_G s) (1 - (starRingEnd ℂ) s.ρ))
  (wp3At_2 : ∀ m : ℕ, ∀ s : OffSeed Xi, wp3At m s ⟨2, by decide⟩ =
      deriv (deriv (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ))

/-- Theorem-level AtOrder coordinate provider from the Route–E quotient-jet provider. -/
instance (priority := 1000)
    [TAC.XiJetWindowIsJetAtOrderQuotProvider] : RouteAJetCoordProviderAt where
  w0At_0 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_w0At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) (s.ρ) (w0At m s) := by
      simpa [IsJet3AtOrderQuot, z_w0At_eq_rho (s := s)] using hq
    -- `IsJet3At` is `A ∧ B ∧ C`
    simpa using h.1
  w0At_1 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_w0At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) (s.ρ) (w0At m s) := by
      simpa [IsJet3AtOrderQuot, z_w0At_eq_rho (s := s)] using hq
    simpa using h.2.1
  w0At_2 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_w0At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) (s.ρ) (w0At m s) := by
      simpa [IsJet3AtOrderQuot, z_w0At_eq_rho (s := s)] using hq
    simpa using h.2.2

  wp2At_0 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp2At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
      simpa [IsJet3AtOrderQuot, TAC.z_wp2At] using hq
    simpa using h.1
  wp2At_1 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp2At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
      simpa [IsJet3AtOrderQuot, TAC.z_wp2At] using hq
    simpa using h.2.1
  wp2At_2 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp2At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
      simpa [IsJet3AtOrderQuot, TAC.z_wp2At] using hq
    simpa using h.2.2

  wp3At_0 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp3At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
      simpa [IsJet3AtOrderQuot, TAC.z_wp3At] using hq
    simpa using h.1
  wp3At_1 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp3At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
      simpa [IsJet3AtOrderQuot, TAC.z_wp3At] using hq
    simpa using h.2.1
  wp3At_2 := by
    intro m s
    have hq : IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) :=
      TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp3At (m := m) (s := s)
    have h : IsJet3At (routeA_G s) (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
      simpa [IsJet3AtOrderQuot, TAC.z_wp3At] using hq
    simpa using h.2.2

end XiPacket
end Targets
end Hyperlocal
