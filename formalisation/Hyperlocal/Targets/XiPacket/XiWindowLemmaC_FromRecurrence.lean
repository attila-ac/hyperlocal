/-
  Hyperlocal/Targets/XiPacket/XiWindowLemmaC_FromRecurrence.lean

  Plan C++ frontier (shrunk further, split cleanly):

  We want `XiLemmaC s` but we do NOT want the recurrence gate to carry more semantics than needed.

  New split:
    • Recurrence extraction is responsible ONLY for the two window consequences:
        ell(w0,wc,wp2)=0,  ell(w0,wc,wp3)=0
    • Anchor nonvanishing is obtained separately via the existing lemma:
        xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0

  Then κ ≠ 0 is derived purely algebraically from the closed form theorem:
      XiLemmaC_kappa_closedForm :
        kappa(reVec3 w0, reVec3 wc, reVec3 ws) = (Xi (sc s)).re

  Finally (JetPivot Move-4 interface): from RecOut we extract exactly:
      hb2 : bCoeff (σ s) (t s) (2:ℝ) = 0
      hb3 : bCoeff (σ s) (t s) (3:ℝ) = 0
  using:
      ell(..., wp_p) = bCoeff(...,p) * kappa(...)
  and κ ≠ 0.

  Net effect:
    The old axiom `xiWindowLemmaC_recOut_fromRecurrence` is now a theorem.
    The only remaining semantic cliff is `xiWindowLemmaC_ell2ell3_fromRecurrence`.
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
Smaller semantic output from “recurrence extraction”:

* `hell2/hell3` are the *actual* recurrence-to-window consequences.
* `hRe` is the explicit nonvanishing target at the critical-line anchor.
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

/-!
## Next Step (Concrete, Minimal): prove the recurrence extraction of the two `ell` vanishings.

This is the only remaining semantic cliff in this file.
Anchor nonvanishing is supplied separately by `xi_sc_re_ne_zero`.
-/

/--
THE (temporary) semantic cliff (minimal):

recurrence extraction yields exactly the two window-level `ell` vanishings.
-/
axiom xiWindowLemmaC_ell2ell3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 ∧
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0

/--
RecOut extraction (theorem form):

* `hell2/hell3` come from the recurrence-extraction lemma above.
* `hRe` comes from the existing anchor nonvanishing lemma `xi_sc_re_ne_zero`.
-/
theorem xiWindowLemmaC_recOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiLemmaC_RecOut s := by
  refine ⟨?_, ?_, ?_⟩
  · exact (xiWindowLemmaC_ell2ell3_fromRecurrence (s := s)).1
  · exact (xiWindowLemmaC_ell2ell3_fromRecurrence (s := s)).2
  · simpa using (xi_sc_re_ne_zero (s := s))

/-- Backwards-compatible name: rebuild the full `XiLemmaC` from the smaller RecOut. -/
theorem xiWindowLemmaC_fromRecurrence (s : Hyperlocal.OffSeed Xi) : XiLemmaC s := by
  exact XiLemmaC_of_recOut (s := s) (xiWindowLemmaC_recOut_fromRecurrence (s := s))

/-!
## JetPivot: extract `hb2/hb3` directly

Move 4 wants the recurrence file to output exactly the two scalar equalities

* `hb2 : bCoeff (σ s) (t s) 2 = 0`
* `hb3 : bCoeff (σ s) (t s) 3 = 0`

This is pure algebra from `RecOut`: use `ell(..., wp) = bCoeff * kappa` plus `kappa ≠ 0`.

IMPORTANT: avoid `simp` on the `hell2/hell3` goals, because simp can unfold
`wc/ws` into basis-window normal forms, breaking definitional matching.
We use `rw` instead.
-/

/-- Internal helper: κ≠0 from `RecOut` (via the closed form κ = Re(Xi(sc))). -/
theorem xi_kappa_ne0_of_recOut (s : Hyperlocal.OffSeed Xi) (h : XiLemmaC_RecOut s) :
    Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
  intro hk0
  have hk :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = (Xi (sc s)).re :=
    XiLemmaC_kappa_closedForm (s := s)
  have hXi0 : (Xi (sc s)).re = 0 := hk.symm.trans hk0
  exact h.hRe hXi0

/-- The requested Move-4 output: `(hb2,hb3)` from recurrence (via `RecOut`). -/
theorem xi_hb2hb3_of_recOut (s : Hyperlocal.OffSeed Xi) (h : XiLemmaC_RecOut s) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧ bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  have hkappa :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 :=
    xi_kappa_ne0_of_recOut (s := s) h

  have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
    have h2 := h.hell2
    rw [ell_wp2_eq_b_mul_kappa (s := s)] at h2
    exact (mul_eq_zero.mp h2).resolve_right hkappa

  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
    have h3 := h.hell3
    rw [ell_wp3_eq_b_mul_kappa (s := s)] at h3
    exact (mul_eq_zero.mp h3).resolve_right hkappa

  exact ⟨hb2, hb3⟩

/-- Final minimal lemma (what Move 4 consumes): `hb2`. -/
theorem xi_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
  (xi_hb2hb3_of_recOut (s := s) (xiWindowLemmaC_recOut_fromRecurrence (s := s))).1

/-- Final minimal lemma (what Move 4 consumes): `hb3`. -/
theorem xi_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
  (xi_hb2hb3_of_recOut (s := s) (xiWindowLemmaC_recOut_fromRecurrence (s := s))).2

theorem xiWindowLemmaC_hell2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 :=
  (xiWindowLemmaC_ell2ell3_fromRecurrence (s := s)).1

theorem xiWindowLemmaC_hell3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 :=
  (xiWindowLemmaC_ell2ell3_fromRecurrence (s := s)).2


end XiPacket
end Targets
end Hyperlocal
