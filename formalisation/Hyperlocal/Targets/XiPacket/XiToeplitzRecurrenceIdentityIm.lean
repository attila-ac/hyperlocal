/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentityIm.lean

  Imag-pivot half only:
    * generic all-primes eliminator from explicit mixed ell-zero hypotheses
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

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder_GenericPrime
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
Generic imag-pivot eliminator.

This is the all-primes version of the local `hb_of` argument:
if the mixed-column ell-functional vanishes on `reVec3 (wpAt m s p)`,
and also vanishes on `reVec3 (w0At m s)`, then `bCoeff(...,p)=0`
provided `kappaAtIm m s ≠ 0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_im_p_of_hell
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    (hk : kappaAtIm m s ≠ 0)
    (hEllW0 :
      Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s)) = 0)
    (hEll :
      Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  classical

  let U0 : Fin 3 → ℝ := imVec3 (w0At m s)
  let Uc : Fin 3 → ℝ := reVec3 (wc s)
  let Us : Fin 3 → ℝ := reVec3 (ws s)

  have ELL_W0 : Transport.ell U0 Uc (reVec3 (w0At m s)) = 0 := by
    simpa [U0, Uc] using hEllW0

  have ELL_P : Transport.ell U0 Uc (reVec3 (wpAt m s p)) = 0 := by
    simpa [U0, Uc] using hEll

  have hkappa : Transport.kappa U0 Uc Us ≠ 0 := by
    simpa [kappaAtIm, U0, Uc, Us] using hk

  have hup :
      reVec3 (wpAt m s p)
        = reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) (p : ℝ)) • Uc
          + (bCoeff (σ s) (t s) (p : ℝ)) • Us := by
    simpa [Uc, Us] using (reVec3_wpAt (m := m) (s := s) (p := p))

  have hsplit :
      Transport.ell U0 Uc
        (reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) (p : ℝ)) • Uc
          + (bCoeff (σ s) (t s) (p : ℝ)) • Us) = 0 := by
    have hEll' := ELL_P
    rw [hup] at hEll'
    exact hEll'

  have hrebr :
      Transport.ell U0 Uc
        ((reVec3 (w0At m s) + (aCoeff (σ s) (t s) (p : ℝ)) • Uc)
          + (bCoeff (σ s) (t s) (p : ℝ)) • Us) = 0 := by
    simpa [add_assoc] using hsplit

  have hsum :
      Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) (p : ℝ)) • Uc)
        + Transport.ell U0 Uc ((bCoeff (σ s) (t s) (p : ℝ)) • Us) = 0 := by
    have hadd :=
      (Transport.ell_add U0 Uc
        (reVec3 (w0At m s) + (aCoeff (σ s) (t s) (p : ℝ)) • Uc)
        ((bCoeff (σ s) (t s) (p : ℝ)) • Us))
    simpa [hadd] using hrebr

  have hUc0 : Transport.ell U0 Uc ((aCoeff (σ s) (t s) (p : ℝ)) • Uc) = 0 := by
    have hsmul := (Transport.ell_smul U0 Uc (aCoeff (σ s) (t s) (p : ℝ)) Uc)
    rw [hsmul]
    rw [ell_uc]
    simp only [mul_zero]

  have hfirst :
      Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) (p : ℝ)) • Uc) = 0 := by
    have hadd := (Transport.ell_add U0 Uc (reVec3 (w0At m s))
      ((aCoeff (σ s) (t s) (p : ℝ)) • Uc))
    have hEq :
        Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) (p : ℝ)) • Uc)
          =
        Transport.ell U0 Uc (reVec3 (w0At m s))
          + Transport.ell U0 Uc ((aCoeff (σ s) (t s) (p : ℝ)) • Uc) := by
      simpa using hadd
    rw [hEq, ELL_W0, hUc0]
    simp only [zero_add, add_zero]

  have hbUs : Transport.ell U0 Uc ((bCoeff (σ s) (t s) (p : ℝ)) • Us) = 0 := by
    have hbUs' := hsum
    rw [hfirst] at hbUs'
    simpa [zero_add] using hbUs'

  have hbκ : (bCoeff (σ s) (t s) (p : ℝ)) * Transport.kappa U0 Uc Us = 0 := by
    have hsmul := (Transport.ell_smul U0 Uc (bCoeff (σ s) (t s) (p : ℝ)) Us)
    have hbEll : (bCoeff (σ s) (t s) (p : ℝ)) * Transport.ell U0 Uc Us = 0 := by
      have hbUs'' := hbUs
      rw [hsmul] at hbUs''
      exact hbUs''
    dsimp [Transport.kappa]
    exact hbEll

  exact (mul_eq_zero.mp hbκ).resolve_right hkappa

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

  have ELL_MIXED :
      Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 ∧
      Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0 := by
    simpa using
      (Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_fromRecurrenceC
        (m := m) (s := s) (hroute := hroute))

  have ELL_W0 :
      Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s)) = 0 := by
    simpa using
      (Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_w0_fromRecurrenceC
        (m := m) (s := s) (hroute := hroute))

  refine ⟨?_, ?_⟩
  · simpa [wp2At] using
      (xiToeplitzRecurrenceIdentity_atOrder_im_p_of_hell
        (m := m) (s := s) (p := 2)
        (hk := hk) (hEllW0 := ELL_W0) (hEll := ELL_MIXED.1))
  · simpa [wp3At] using
      (xiToeplitzRecurrenceIdentity_atOrder_im_p_of_hell
        (m := m) (s := s) (p := 3)
        (hk := hk) (hEllW0 := ELL_W0) (hEll := ELL_MIXED.2))

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

/--
Generic-prime mixed imag-pivot theorem surface.

This is the imag-pivot companion to the real theorem above:
once the upstream lane can provide row-0 zero for `wpAt m s p`, the mixed
imag-pivot identity immediately yields `bCoeff(...,p)=0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_im_p_of_row0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk : kappaAtIm m s ≠ 0)
    (hwpop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact xiToeplitzRecurrenceIdentity_atOrder_im_p_of_hell
    (m := m) (s := s) (p := p)
    (hk := hk)
    (hEllW0 := xiToeplitzEllOutAtImRe_w0_fromRecurrenceC
      (m := m) (s := s) (hroute := hroute))
    (hEll := xiToeplitzEllOutAtImRe_p_fromRecurrenceC_of_row0
      (m := m) (s := s) (p := p)
      (hroute := hroute)
      (hwpop := hwpop))

end XiPacket
end Targets
end Hyperlocal
