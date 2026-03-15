import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentity_GenericPrimeFromRec2AtOrder
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcScalarClosedForm
import Hyperlocal.Targets.XiPacket.XiDslopeToKappaAtOrder
import Hyperlocal.Targets.ZetaTransfer
import Hyperlocal.Cancellation.TwoPrimePhaseLock
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
For a fixed off-seed `s`, a Route–A scalar-zero theorem already forces
`bCoeff(σ(s), t(s), p)=0` for arbitrary prime windows `p`, using the new
generic-prime Rec2 → row0 → identity route.
-/
theorem xiBcoeff_p_eq_zero_of_routeA_scalar
    (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  classical

  let m : ℕ := Classical.choose (xiJetNonflat_dslope_exists (s := s))
  have hmDs : XiPacket.dslopeIterAt (m := m) (s := s) ≠ 0 :=
    Classical.choose_spec (xiJetNonflat_dslope_exists (s := s))

  have hKap :
      (Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) :=
    hkappaAt_of_dslopeIter_ne0 (m := m) (s := s) hmDs

  cases hKap with
  | inl hRe =>
      exact xiToeplitzRecurrenceIdentity_atOrder_p_of_trueAnalyticPrime
        (m := m) (s := s) (p := p)
        (hroute := hroute) (hk := hRe)
  | inr hIm =>
      exact xiToeplitzRecurrenceIdentity_atOrder_im_p_of_trueAnalyticPrime
        (m := m) (s := s) (p := p)
        (hroute := hroute) (hk := hIm)

/--
The corresponding sine vanishing for an arbitrary prime index `p`.
-/
theorem xiSinLogPrime_eq_zero_of_routeA_scalar
    (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Real.sin ((t s) * Real.log (p : ℝ)) = 0 := by
  exact
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (p : ℝ))
      (hb := xiBcoeff_p_eq_zero_of_routeA_scalar
        (s := s) (p := p) (hroute := hroute))
/--
For a fixed off-seed `s`, a Route–A scalar-zero theorem already forces
`bCoeff(σ(s), t(s), 2)=0`, using only the existing `{2,3}` identity route.
-/
theorem xiBcoeff2_eq_zero_of_routeA_scalar
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  classical

  let m : ℕ := Classical.choose (xiJetNonflat_dslope_exists (s := s))
  have hmDs : XiPacket.dslopeIterAt (m := m) (s := s) ≠ 0 :=
    Classical.choose_spec (xiJetNonflat_dslope_exists (s := s))

  have hKap :
      (Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) :=
    hkappaAt_of_dslopeIter_ne0 (m := m) (s := s) hmDs

  cases hKap with
  | inl hRe =>
      exact
        (xiToeplitzRecurrenceIdentity_atOrder
          (m := m) (s := s) (hroute := hroute) (hk := hRe)).1
  | inr hIm =>
      exact
        (xiToeplitzRecurrenceIdentity_atOrder_im
          (m := m) (s := s) (hroute := hroute) (hk := hIm)).1

/--
For a fixed off-seed `s`, a Route–A scalar-zero theorem already forces
`bCoeff(σ(s), t(s), 3)=0`, using only the existing `{2,3}` identity route.
-/
theorem xiBcoeff3_eq_zero_of_routeA_scalar
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  classical

  let m : ℕ := Classical.choose (xiJetNonflat_dslope_exists (s := s))
  have hmDs : XiPacket.dslopeIterAt (m := m) (s := s) ≠ 0 :=
    Classical.choose_spec (xiJetNonflat_dslope_exists (s := s))

  have hKap :
      (Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) :=
    hkappaAt_of_dslopeIter_ne0 (m := m) (s := s) hmDs

  cases hKap with
  | inl hRe =>
      exact
        (xiToeplitzRecurrenceIdentity_atOrder
          (m := m) (s := s) (hroute := hroute) (hk := hRe)).2
  | inr hIm =>
      exact
        (xiToeplitzRecurrenceIdentity_atOrder_im
          (m := m) (s := s) (hroute := hroute) (hk := hIm)).2

/-- The prime-2 sine vanishing forced by a Route–A scalar-zero theorem. -/
theorem xiSinLog2_eq_zero_of_routeA_scalar
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  exact
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (2 : ℝ))
      (hb := xiBcoeff2_eq_zero_of_routeA_scalar
        (s := s) (hroute := hroute))

/-- The prime-3 sine vanishing forced by a Route–A scalar-zero theorem. -/
theorem xiSinLog3_eq_zero_of_routeA_scalar
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
  exact
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (3 : ℝ))
      (hb := xiBcoeff3_eq_zero_of_routeA_scalar
        (s := s) (hroute := hroute))

/--
A global Route–A scalar theorem immediately refutes any off-seed of `Ξ`,
using only the two primes `2` and `3`.
-/
theorem offSeed_false_of_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (s : Hyperlocal.OffSeed Xi) :
    False := by
  have hsin2 : Real.sin ((t s) * Real.log (2 : ℝ)) = 0 :=
    xiSinLog2_eq_zero_of_routeA_scalar
      (s := s) (hroute := hroute s)

  have hsin3 : Real.sin ((t s) * Real.log (3 : ℝ)) = 0 :=
    xiSinLog3_eq_zero_of_routeA_scalar
      (s := s) (hroute := hroute s)

  have ht0 : t s = 0 :=
    Hyperlocal.Cancellation.PrimeWitness.two_prime_phase_lock (t s) ⟨hsin2, hsin3⟩

  have ht_ne : t s ≠ 0 := by
    simpa [XiPacket.t] using s.ht

  exact ht_ne ht0

/--
Direct Xi-side endgame:
a global Route–A scalar-zero theorem already implies `NoOffSeed Xi`.
-/
theorem noOffSeed_Xi_of_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Xi := by
  intro hne
  rcases hne with ⟨s⟩
  exact offSeed_false_of_routeA_scalar (hroute := hroute) (s := s)

/--
Direct ζ-side transfer from the same global Route–A scalar theorem.
-/
theorem noOffSeed_Zeta_of_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
    exact noOffSeed_Xi_of_routeA_scalar (hroute := hroute)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
Direct RH-facing pointwise export from the same global Route–A scalar theorem.
-/
theorem criticalzero_zeta_of_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0) (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
      exact noOffSeed_Xi_of_routeA_scalar (hroute := hroute)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi)
    (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
