/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentityIm.lean

  Imag-pivot half only:
    * order-m lemma consuming `kappaAtIm m s ≠ 0`
    * pivot-gate `{2,3}` wrapper (Re or Im witness)

  Design constraints:
    - never simp-expand `wc` into basis vectors
    - avoid simp recursion; prefer explicit rewrites (`rw`, `dsimp`, `simp only`)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityRe
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderIm
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaPivotNonzero
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

/--
Identity route at order `m` (imag pivot):

mixed-column ell-out at order `m` + `kappaAtIm m s ≠ 0` ⇒ `bCoeff(2)=0 ∧ bCoeff(3)=0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_im
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hk : kappaAtIm m s ≠ 0) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  classical

  -- Shorthand columns (avoid unfolding later)
  let U0 : Fin 3 → ℝ := imVec3 (w0At m s)
  let Uc : Fin 3 → ℝ := reVec3 (wc s)
  let Us : Fin 3 → ℝ := reVec3 (ws s)

  have ELL_MIXED :
      Transport.ell U0 Uc (reVec3 (wp2At m s)) = 0 ∧
      Transport.ell U0 Uc (reVec3 (wp3At m s)) = 0 := by
    simpa [U0, Uc] using
      (Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_fromRecurrenceC (m := m) (s := s))

  have ELL_W0 :
      Transport.ell U0 Uc (reVec3 (w0At m s)) = 0 := by
    simpa [U0, Uc] using
      (Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_w0_fromRecurrenceC (m := m) (s := s))

  have hkappa : Transport.kappa U0 Uc Us ≠ 0 := by
    -- keep simp small; only unfolds kappaAtIm and our local lets
    simpa [kappaAtIm, U0, Uc, Us] using hk

  -- helper: from ell(up)=0 and reVec3(up)=w0 + a·Uc + b·Us, get b=0
  have hb_of (p : ℝ) (up : Window 3)
      (hup :
        reVec3 up =
          reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) p) • Uc
          + (bCoeff (σ s) (t s) p) • Us)
      (hEll : Transport.ell U0 Uc (reVec3 up) = 0) :
      bCoeff (σ s) (t s) p = 0 := by

    -- rewrite hEll using hup (NO simp)
    have hsplit :
        Transport.ell U0 Uc
          (reVec3 (w0At m s)
            + (aCoeff (σ s) (t s) p) • Uc
            + (bCoeff (σ s) (t s) p) • Us) = 0 := by
      have hEll' := hEll
      rw [hup] at hEll'
      exact hEll'

    -- rebracket: (w0 + a·Uc) + (b·Us)
    have hrebr :
        Transport.ell U0 Uc
          ((reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
            + (bCoeff (σ s) (t s) p) • Us) = 0 := by
      -- assoc only
      simpa [add_assoc] using hsplit

    have hsum :
        Transport.ell U0 Uc (reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
          + Transport.ell U0 Uc ((bCoeff (σ s) (t s) p) • Us) = 0 := by
      have hadd :=
        (Transport.ell_add U0 Uc
          (reVec3 (w0At m s) + (aCoeff (σ s) (t s) p) • Uc)
          ((bCoeff (σ s) (t s) p) • Us))
      -- DO NOT simp; just rewrite hrebr using hadd
      simpa [hadd] using hrebr

    -- ell(a·Uc)=0 via ell_smul + ell_uc, with rw/dsimp only
    have hUc0 : Transport.ell U0 Uc ((aCoeff (σ s) (t s) p) • Uc) = 0 := by
      have hsmul := (Transport.ell_smul U0 Uc (aCoeff (σ s) (t s) p) Uc)
      -- hsmul : ell(..., a•Uc) = a * ell(...,Uc)
      rw [hsmul]
      -- now reduce to a * 0 = 0
      -- IMPORTANT: avoid simp recursion; rewrite ell_uc then simp only mul_zero
      rw [ell_uc]
      simp only [mul_zero]

    -- ell(w0 + a·Uc)=0 via ell_add + (ELL_W0, hUc0)
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

    -- hence ell(b·Us)=0 without simp recursion
    have hbUs : Transport.ell U0 Uc ((bCoeff (σ s) (t s) p) • Us) = 0 := by
      have hbUs' := hsum
      rw [hfirst] at hbUs'
      -- hbUs' : 0 + ell(...) = 0
      simpa [zero_add] using hbUs'

    -- convert ell(b·Us)=0 into b * kappa = 0, then cancel hkappa
    have hbκ : (bCoeff (σ s) (t s) p) * Transport.kappa U0 Uc Us = 0 := by
      have hsmul := (Transport.ell_smul U0 Uc (bCoeff (σ s) (t s) p) Us)
      -- rewrite hbUs using ell_smul, NO simp
      have hbEll : (bCoeff (σ s) (t s) p) * Transport.ell U0 Uc Us = 0 := by
        have hbUs'' := hbUs
        rw [hsmul] at hbUs''
        exact hbUs''
      -- unfold kappa in a controlled way
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
    [XiKappaPivotNonzero s]
    (p : ℝ) (hp : p = (2 : ℝ) ∨ p = (3 : ℝ)) :
    bCoeff (σ s) (t s) p = 0 := by
  classical
  rcases (xiKappaPivotNonzero_out (s := s)) with hRe | hIm
  ·
    rcases hRe with ⟨m, hk⟩
    have hb := xiToeplitzRecurrenceIdentity_atOrder (m := m) (s := s) hk
    rcases hp with rfl | rfl
    · exact hb.1
    · exact hb.2
  ·
    rcases hIm with ⟨m, hk⟩
    have hb := xiToeplitzRecurrenceIdentity_atOrder_im (m := m) (s := s) hk
    rcases hp with rfl | rfl
    · exact hb.1
    · exact hb.2

end XiPacket
end Targets
end Hyperlocal
