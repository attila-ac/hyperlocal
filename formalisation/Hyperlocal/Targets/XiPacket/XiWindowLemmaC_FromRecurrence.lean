/-
  Hyperlocal/Targets/XiPacket/XiWindowLemmaC_FromRecurrence.lean

  Plan C++ frontier (shrunk further, split cleaner):

  We want to eliminate the “prime-phase-lock” axioms from the ξ-window pipeline.

  Current state:

  * Move-4 wants (hb2,hb3):
      hb2 : bCoeff (σ s) (t s) 2 = 0
      hb3 : bCoeff (σ s) (t s) 3 = 0

  * We now PROVE (hb2,hb3) from the *actual Toeplitz/recurrence output*,
    phrased canonically as the two window-level determinant vanishings:

      ell(w0,wc,wp2)=0,  ell(w0,wc,wp3)=0

    plus the already-separated anchor nonvanishing:

      xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0

    and the closed form:

      XiLemmaC_kappa_closedForm :
        kappa(reVec3 w0, reVec3 wc, reVec3 ws) = (Xi (sc s)).re

  Net effect:

  * The old cliff `xiWindowLemmaC_hb2hb3_fromRecurrence` is now a THEOREM.
  * The only remaining semantic cliff in this file is the Toeplitz/recurrence
    extraction of the two ell-vanishings, packaged as `xiToeplitzEllOut_fromRecurrence`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowLemmaC
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappa
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Canonical “Toeplitz/recurrence extraction” output at the window level:

it yields exactly the two `ell`-vanishings for `p=2,3`.
This is the right place to later connect ξ-transport/Toeplitz infrastructure.
-/
structure XiToeplitzEllOut (s : Hyperlocal.OffSeed Xi) : Prop where
  hell2 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0
  hell3 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0

/--
THE (temporary) semantic cliff (now in the correct layer):

Toeplitz/recurrence extraction yields the two window-level `ell`-vanishings.
-/
axiom xiToeplitzEllOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
  XiToeplitzEllOut s

/-- Convenience projections. -/
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

`hb2/hb3` are now THEOREMS obtained by rewriting from the Toeplitz/recurrence
`ell`-vanishings and using κ≠0 from the anchor.
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

* `hell2/hell3` are the window-level `ell` vanishings (coming from Toeplitz/recurrence).
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

* `hell2/hell3` come from `xiToeplitzEllOut_fromRecurrence`.
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
