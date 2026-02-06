/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_RecurrenceToEllKappa.lean

  Phase 3C: Lemma C scaffolding.

  This file proves the *algebraic* layer now:
    - how `reVec3` interacts with the trig-split definitional windows
    - how `ell` reduces to `bCoeff * kappa` under trig-split

  The only remaining semantic burden is isolated as `XiLemmaC_Core`,
  which you will later prove from the actual ξ windowed recurrence/coupling.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

-- IMPORTANT:
-- `ell/kappa/Window` live in `Hyperlocal.Transport` (not a sub-namespace).
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Convenience simp: real-part of `(r : ℂ) * z` for real `r`. -/
@[simp] lemma re_ofReal_mul (r : ℝ) (z : ℂ) :
    (((r : ℂ) * z).re) = r * z.re := by
  simp [Complex.mul_re]

/-- Real-part vectorization commutes with scaling by a real scalar embedded in `ℂ`. -/
lemma reVec3_smul_ofReal (a : ℝ) (w : Window 3) :
    reVec3 ((a : ℂ) • w) = a • reVec3 w := by
  funext i
  simp [reVec3]

/-- `reVec3` trig-split for `wp2` (purely from definitions). -/
lemma reVec3_wp2 (s : _root_.Hyperlocal.OffSeed Xi) :
    reVec3 (wp2 s)
      = reVec3 (w0 s)
        + (aCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (wc s)
        + (bCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (ws s) := by
  funext i
  -- unfold `reVec3`, `wp2`; push `.re` through sums; simplify `((r:ℂ)*z).re`
  simp [reVec3, wp2, Complex.add_re, Pi.add_apply, Pi.smul_apply,
        add_assoc, add_left_comm, add_comm]

/-- `reVec3` trig-split for `wp3` (purely from definitions). -/
lemma reVec3_wp3 (s : _root_.Hyperlocal.OffSeed Xi) :
    reVec3 (wp3 s)
      = reVec3 (w0 s)
        + (aCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (wc s)
        + (bCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (ws s) := by
  funext i
  simp [reVec3, wp3, Complex.add_re, Pi.add_apply, Pi.smul_apply,
        add_assoc, add_left_comm, add_comm]

/-- Determinant identity: under trig-split, `ell` collapses to `b * kappa`. -/
lemma ell_of_trigSplit (u0 uc us : Fin 3 → ℝ) (a b : ℝ) :
    ell u0 uc (u0 + a • uc + b • us) = b * kappa u0 uc us := by
  classical
  calc
    ell u0 uc (u0 + a • uc + b • us)
        = ell u0 uc (u0 + (a • uc + b • us)) := by
            simp [add_assoc]
    _ = ell u0 uc u0 + ell u0 uc (a • uc + b • us) := by
            simpa using (ell_add u0 uc u0 (a • uc + b • us))
    _ = ell u0 uc (a • uc + b • us) := by
            simp [ell_u0]
    _ = ell u0 uc (a • uc) + ell u0 uc (b • us) := by
            simpa using (ell_add u0 uc (a • uc) (b • us))
    _ = a * ell u0 uc uc + b * ell u0 uc us := by
            simp [ell_smul, add_assoc, add_left_comm, add_comm]
    _ = b * kappa u0 uc us := by
            simp [ell_uc, ell_us_eq_kappa]

/-- Specialized collapse for p=2 (uses only definitional `wp2`). -/
lemma ell_wp2_eq_b_mul_kappa (s : _root_.Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s))
      =
      (bCoeff (σ s) (t s) (2 : ℝ))
        * kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  have hsplit := reVec3_wp2 (s := s)
  simpa [hsplit, add_assoc] using
    (ell_of_trigSplit
      (u0 := reVec3 (w0 s))
      (uc := reVec3 (wc s))
      (us := reVec3 (ws s))
      (a  := aCoeff (σ s) (t s) (2 : ℝ))
      (b  := bCoeff (σ s) (t s) (2 : ℝ)))

/-- Specialized collapse for p=3 (uses only definitional `wp3`). -/
lemma ell_wp3_eq_b_mul_kappa (s : _root_.Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s))
      =
      (bCoeff (σ s) (t s) (3 : ℝ))
        * kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  have hsplit := reVec3_wp3 (s := s)
  simpa [hsplit, add_assoc] using
    (ell_of_trigSplit
      (u0 := reVec3 (w0 s))
      (uc := reVec3 (wc s))
      (us := reVec3 (ws s))
      (a  := aCoeff (σ s) (t s) (3 : ℝ))
      (b  := bCoeff (σ s) (t s) (3 : ℝ)))

/-
  The semantic residue for Lemma C.

  Ultimately proved from the real ξ windowed recurrence/coupling.
  For now this is the exact minimal target that feeds the Phase-4 builder.
-/
structure XiLemmaC_Core (s : _root_.Hyperlocal.OffSeed Xi) : Prop where
  hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0
  hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0
  hkappa : kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0

/-- Core ⇒ the exact `hell2` field expected by `WindowPayload`. -/
theorem XiLemmaC_hell2_of_core (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Core s) :
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 := by
  calc
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s))
        =
        (bCoeff (σ s) (t s) (2 : ℝ))
          * kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using ell_wp2_eq_b_mul_kappa (s := s)
    _ = 0 := by simp [h.hb2]

/-- Core ⇒ the exact `hell3` field expected by `WindowPayload`. -/
theorem XiLemmaC_hell3_of_core (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Core s) :
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 := by
  calc
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s))
        =
        (bCoeff (σ s) (t s) (3 : ℝ))
          * kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using ell_wp3_eq_b_mul_kappa (s := s)
    _ = 0 := by simp [h.hb3]

end XiPacket
end Targets
end Hyperlocal
