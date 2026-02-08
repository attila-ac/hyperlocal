/-
  Hyperlocal/Targets/XiPacket/XiWindowLemmaC_FromRecurrence.lean

  Plan C++ frontier (shrunk further, split cleaner):

  We want to eliminate the “prime-phase-lock” assumptions from the ξ-window pipeline.

  Current state:

  * Move-4 wants (hb2,hb3):
      hb2 : bCoeff (σ s) (t s) 2 = 0
      hb3 : bCoeff (σ s) (t s) 3 = 0

  * The only remaining Toeplitz/recurrence semantic cliff has been moved out of
    this file into `XiToeplitzRecurrenceBridge.lean` as:
        xiToeplitzSpanOut_fromRecurrence

    This file only consumes the Toeplitz extraction output (ℓ vanishings),
    plus the anchor nonvanishing, and derives everything else algebraically.

  Anchor nonvanishing remains separate via:
      xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0

  κ ≠ 0 is derived purely algebraically from the closed form theorem:
      XiLemmaC_kappa_closedForm :
        kappa(reVec3 w0, reVec3 wc, reVec3 ws) = (Xi (sc s)).re
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiWindowLemmaC
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappa
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceBridge
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Convenience projections: the two `ell` vanishings from Toeplitz extraction. -/
theorem xiWindowLemmaC_hell2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 :=
  (xiToeplitzEllOut_fromRecurrence (s := s)).hell2

theorem xiWindowLemmaC_hell3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 :=
  (xiToeplitzEllOut_fromRecurrence (s := s)).hell3

theorem xiWindowLemmaC_ell2ell3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 ∧
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 :=
  ⟨xiWindowLemmaC_hell2_fromRecurrence (s := s),
   xiWindowLemmaC_hell3_fromRecurrence (s := s)⟩

/-- κ≠0 from the anchor nonvanishing plus the κ closed form. -/
theorem xi_kappa_ne0_from_anchor (s : Hyperlocal.OffSeed Xi) :
    Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
  intro hk0
  have hk :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
        = (Xi (sc s)).re :=
    XiLemmaC_kappa_closedForm (s := s)
  have hXi0 : (Xi (sc s)).re = 0 := hk.symm.trans hk0
  exact (xi_sc_re_ne_zero (s := s)) hXi0

/--
KEY SHRINK RESULT:

`hb2/hb3` are theorems obtained by rewriting from the Toeplitz-extracted `ell`-vanishings
and using κ≠0 from the anchor.
-/
theorem xiWindowLemmaC_hb2hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧ bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  have hkappa :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 :=
    xi_kappa_ne0_from_anchor (s := s)

  have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
    have h2 := xiWindowLemmaC_hell2_fromRecurrence (s := s)
    rw [ell_wp2_eq_b_mul_kappa (s := s)] at h2
    exact (mul_eq_zero.mp h2).resolve_right hkappa

  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
    have h3 := xiWindowLemmaC_hell3_fromRecurrence (s := s)
    rw [ell_wp3_eq_b_mul_kappa (s := s)] at h3
    exact (mul_eq_zero.mp h3).resolve_right hkappa

  exact ⟨hb2, hb3⟩

/-- Move-4 outputs as direct projections. -/
theorem xi_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
  (xiWindowLemmaC_hb2hb3_fromRecurrence (s := s)).1

theorem xi_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
  (xiWindowLemmaC_hb2hb3_fromRecurrence (s := s)).2

/--
Smaller semantic output from “recurrence extraction” used by `XiLemmaC` plumbing:

* `hell2/hell3` are the window-level `ell` vanishings (coming from Toeplitz extraction).
* `hRe` is the explicit anchor nonvanishing.
-/
structure XiLemmaC_RecOut (s : Hyperlocal.OffSeed Xi) : Prop where
  hell2 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0
  hell3 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0
  hRe :
    (Xi (sc s)).re ≠ 0

/-- Pure algebra: `XiLemmaC_RecOut` already implies the full `XiLemmaC`. -/
theorem XiLemmaC_of_recOut (s : Hyperlocal.OffSeed Xi) (h : XiLemmaC_RecOut s) :
    XiLemmaC s := by
  refine ⟨h.hell2, h.hell3, ?_⟩
  intro hk0
  have hk :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
        = (Xi (sc s)).re :=
    XiLemmaC_kappa_closedForm (s := s)
  have hXi0 : (Xi (sc s)).re = 0 :=
    hk.symm.trans hk0
  exact h.hRe hXi0

/--
RecOut extraction (theorem form):

* `hell2/hell3` come from Toeplitz extraction (`xiToeplitzEllOut_fromRecurrence`).
* `hRe` comes from `xi_sc_re_ne_zero`.
-/
theorem xiWindowLemmaC_recOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiLemmaC_RecOut s := by
  refine ⟨?_, ?_, ?_⟩
  · exact xiWindowLemmaC_hell2_fromRecurrence (s := s)
  · exact xiWindowLemmaC_hell3_fromRecurrence (s := s)
  · simpa using (xi_sc_re_ne_zero (s := s))

/-- Backwards-compatible name: rebuild the full `XiLemmaC` from the smaller RecOut. -/
theorem xiWindowLemmaC_fromRecurrence (s : Hyperlocal.OffSeed Xi) : XiLemmaC s := by
  exact XiLemmaC_of_recOut (s := s) (xiWindowLemmaC_recOut_fromRecurrence (s := s))

end XiPacket
end Targets
end Hyperlocal
