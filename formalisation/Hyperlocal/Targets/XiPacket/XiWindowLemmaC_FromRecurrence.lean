/-
  Hyperlocal/Targets/XiPacket/XiWindowLemmaC_FromRecurrence.lean

  Plan C++ frontier (shrunk further):

  Instead of axiomatizing the full `XiLemmaC s` (which included κ ≠ 0),
  we axiomatize only the two recurrence consequences

      ell(w0,wc,wp2)=0,  ell(w0,wc,wp3)=0

  plus ONE explicit nonvanishing target at the critical-line anchor:

      (Xi (sc s)).re ≠ 0

  Then κ ≠ 0 is derived purely algebraically from the closed form theorem

      XiLemmaC_kappa_closedForm :
        kappa(reVec3 w0, reVec3 wc, reVec3 ws) = (Xi (sc s)).re

  Finally (JetPivot Move-4 interface): from RecOut we extract exactly

      hb2 : bCoeff (σ s) (t s) (2:ℝ) = 0
      hb3 : bCoeff (σ s) (t s) (3:ℝ) = 0

  using the determinant identity
      ell(..., wp_p) = bCoeff(...,p) * kappa(...)
  and κ ≠ 0.
-/

import Hyperlocal.Targets.XiPacket.XiWindowLemmaC
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
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
* `hRe` is the only remaining nonvanishing semantic target (explicit and recognizable).
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
  -- Prove κ ≠ 0 by contradiction using the closed form κ = Re(Xi(sc)).
  intro hk0
  have hk :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
        = (Xi (sc s)).re :=
    XiLemmaC_kappa_closedForm (s := s)
  have hXi0 : (Xi (sc s)).re = 0 :=
    hk.symm.trans hk0
  exact h.hRe hXi0

/--
THE (temporary) semantic cliff, now strictly smaller:

recurrence extraction yields the two ell-vanishings plus the explicit `Re(Xi(sc)) ≠ 0`.
-/
axiom xiWindowLemmaC_recOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiLemmaC_RecOut s

/-- Backwards-compatible name: rebuild the full `XiLemmaC` from the smaller RecOut. -/
theorem xiWindowLemmaC_fromRecurrence (s : Hyperlocal.OffSeed Xi) : XiLemmaC s := by
  exact XiLemmaC_of_recOut (s := s) (xiWindowLemmaC_recOut_fromRecurrence (s := s))

/-!
## JetPivot: extract `hb2/hb3` directly

Move 4 wants the recurrence file to output exactly the two scalar equalities

* `hb2 : bCoeff (σ s) (t s) 2 = 0`
* `hb3 : bCoeff (σ s) (t s) 3 = 0`

This is pure algebra from `RecOut`: use the determinant identity
`ell(..., wp) = bCoeff * kappa` plus `kappa ≠ 0`.

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
    -- Rewrite (no simp): turn ell(...,wp2)=0 into (bCoeff*κ)=0.
    rw [ell_wp2_eq_b_mul_kappa (s := s)] at h2
    exact (mul_eq_zero.mp h2).resolve_right hkappa

  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
    have h3 := h.hell3
    -- Rewrite (no simp): turn ell(...,wp3)=0 into (bCoeff*κ)=0.
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

end XiPacket
end Targets
end Hyperlocal
