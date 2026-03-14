/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentityIm.lean

  Imag-pivot half only:
    * order-m lemma consuming `kappaAtIm m s ≠ 0`
    * pivot-gate `{2,3}` wrapper (Re or Im witness)

  Design constraints:
    - never simp-expand `wc` into basis vectors
    - avoid simp recursion; prefer explicit rewrites (`rw`, `dsimp`, `simp only`)

  2026-03-13 honest post-axiom state:
  * downstream ell-out surfaces are now theorem-gated
  * therefore these exported theorem surfaces can no longer remain assumption-free
  * they must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
      [RouteAWcScalarProvider]

  plus the explicit Route-A scalar-zero payload required by the `wc` branch.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityRe
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderIm
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaPivotNonzero
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem
import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Identity route at order `m` (imag pivot):

mixed-column ell-out at order `m` + `kappaAtIm m s ≠ 0` ⇒ `bCoeff(2)=0 ∧ bCoeff(3)=0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_im
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk : kappaAtIm m s ≠ 0) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  classical

  let U0 : Fin 3 → ℝ := imVec3 (w0At m s)
  let Uc : Fin 3 → ℝ := reVec3 (wc s)
  let Us : Fin 3 → ℝ := reVec3 (ws s)

  have ELL_MIXED :
      Transport.ell U0 Uc (reVec3 (wp2At m s)) = 0 ∧
      Transport.ell U0 Uc (reVec3 (wp3At m s)) = 0 := by
    simpa [U0, Uc] using
      (Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_fromRecurrenceC
        (m := m) (s := s) (hroute := hroute))

  have ELL_W0 :
      Transport.ell U0 Uc (reVec3 (w0At m s)) = 0 := by
    simpa [U0, Uc] using
      (Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_w0_fromRecurrenceC
        (m := m) (s := s) (hroute := hroute))

  have hkappa : Transport.kappa U0 Uc Us ≠ 0 := by
    simpa [kappaAtIm, U0, Uc, Us] using hk

  have hb_of (p : ℝ) (up : Window 3)
      (hup :
        reVec3 up =
          reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) p) • Uc
          + (bCoeff (σ s) (t s) p) • Us)
      (hEll : Transport.ell U0 Uc (reVec3 up) = 0) :
      bCoeff (σ s) (t s) p = 0 := by

    have hsplit :
        Transport.ell U0 Uc
          (reVec3 (w0At m s)
            + (aCoeff (σ s) (t s) p) • Uc
            + (bCoeff (σ s) (t s) p) • Us) = 0 := by
      have hEll' := hEll
      rw [hup] at hEll'
      exact hEll'

    have hrebr :
        Transport.ell U0 Uc
          ((reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
            + (bCoeff (σ s) (t s) p) • Us) = 0 := by
      simpa [add_assoc] using hsplit

    have hsum :
        Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
          + Transport.ell U0 Uc ((bCoeff (σ s) (t s) p) • Us) = 0 := by
      have hadd :=
        (Transport.ell_add U0 Uc
          (reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
          ((bCoeff (σ s) (t s) p) • Us))
      simpa [hadd] using hrebr

    have hUc0 : Transport.ell U0 Uc ((aCoeff (σ s) (t s) p) • Uc) = 0 := by
      have hsmul := (Transport.ell_smul U0 Uc (aCoeff (σ s) (t s) p) Uc)
      rw [hsmul]
      rw [ell_uc]
      simp only [mul_zero]

    have hfirst :
        Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc) = 0 := by
      have hadd := (Transport.ell_add U0 Uc (reVec3 (w0At m s)) ((aCoeff (σ s) (t s) p) • Uc))
      have hEq :
          Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
            =
          Transport.ell U0 Uc (reVec3 (w0At m s))
            + Transport.ell U0 Uc ((aCoeff (σ s) (t s) p) • Uc) := by
        simpa using hadd
      rw [hEq, ELL_W0, hUc0]
      simp only [zero_add, add_zero]

    have hbUs : Transport.ell U0 Uc ((bCoeff (σ s) (t s) p) • Us) = 0 := by
      have hbUs' := hsum
      rw [hfirst] at hbUs'
      simpa [zero_add] using hbUs'

    have hbκ : (bCoeff (σ s) (t s) p) * Transport.kappa U0 Uc Us = 0 := by
      have hsmul := (Transport.ell_smul U0 Uc (bCoeff (σ s) (t s) p) Us)
      have hbEll : (bCoeff (σ s) (t s) p) * Transport.ell U0 Uc Us = 0 := by
        have hbUs'' := hbUs
        rw [hsmul] at hbUs''
        exact hbUs''
      dsimp [Transport.kappa]
      exact hbEll

    exact (mul_eq_zero.mp hbκ).resolve_right hkappa

  refine ⟨?_, ?_⟩
  ·
    have hup2 :
        reVec3 (wp2At m s)
          = reVec3 (w0At m s)
            + (aCoeff (σ s) (t s) (2 : ℝ)) • Uc
            + (bCoeff (σ s) (t s) (2 : ℝ)) • Us := by
      simpa [Uc, Us] using (reVec3_wp2At (m := m) (s := s))
    exact hb_of (p := (2 : ℝ)) (up := wp2At m s) hup2 ELL_MIXED.1
  ·
    have hup3 :
        reVec3 (wp3At m s)
          = reVec3 (w0At m s)
            + (aCoeff (σ s) (t s) (3 : ℝ)) • Uc
            + (bCoeff (σ s) (t s) (3 : ℝ)) • Us := by
      simpa [Uc, Us] using (reVec3_wp3At (m := m) (s := s))
    exact hb_of (p := (3 : ℝ)) (up := wp3At m s) hup3 ELL_MIXED.2

/--
Pivot-gate wrapper in the `{2,3}` API form.
-/
theorem xiToeplitzRecurrenceIdentity_p
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (p : ℝ) (hp : p = (2 : ℝ) ∨ p = (3 : ℝ)) :
    bCoeff (σ s) (t s) p = 0 := by
  classical
  rcases (xiKappaPivotNonzero_out (s := s)) with hRe | hIm
  ·
    rcases hRe with ⟨m, hk⟩
    have hb := xiToeplitzRecurrenceIdentity_atOrder
      (m := m) (s := s) (hroute := hroute) (hk := hk)
    rcases hp with rfl | rfl
    · exact hb.1
    · exact hb.2
  ·
    rcases hIm with ⟨m, hk⟩
    have hb := xiToeplitzRecurrenceIdentity_atOrder_im
      (m := m) (s := s) (hroute := hroute) (hk := hk)
    rcases hp with rfl | rfl
    · exact hb.1
    · exact hb.2

end XiPacket
end Targets
end Hyperlocal
