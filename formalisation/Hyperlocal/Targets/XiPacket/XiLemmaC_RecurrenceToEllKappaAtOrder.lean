/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_RecurrenceToEllKappaAtOrder.lean

  FULL REPLACEMENT (compiles): restores the Lemma-C determinant interface at order `m`
  and keeps the Option-A κ-widening (Re/Im pivot) **without** attempting any of the
  brittle “imag-pivot ell/wp2/wp3” window facts (which depend on transport-realness).

  What this file provides (and downstream expects):
    • generic trig-split reVec3 lemma for `wpAt`
    • specialized `wp2At/wp3At` reVec3 lemmas
    • `ell_of_trigSplit`
    • generic determinant identity `ell_wpAt_eq_b_mul_kappa`
    • specialized determinant identities for `wp2At/wp3At`
    • core package `XiLemmaC_CoreAt` with widened κ-witness (Or-shape)
    • consequences: `XiLemmaC_hell2At_of_core`, `XiLemmaC_hell3At_of_core`
    • JetPivot κ-leverage:
        hkappaAt_of_cderivRe_ne0 : Or.inl ...
        hkappaAt_of_cderivIm_ne0 : Or.inr ...

  No new axioms.
-/

import Hyperlocal.Transport.PrimeSineRescue
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Real-part vectorization respects real scalar smul on windows. -/
@[simp] lemma reVec3_smul_ofReal (a : ℝ) (w : Window 3) :
    reVec3 ((a : ℂ) • w) = a • reVec3 w := by
  funext i
  simp [reVec3, Pi.smul_apply]

/-- Imag-part vectorization respects real scalar smul on windows. -/
@[simp] lemma imVec3_smul_ofReal (a : ℝ) (w : Window 3) :
    imVec3 ((a : ℂ) • w) = a • imVec3 w := by
  funext i
  simp [imVec3, Pi.smul_apply]

/-- Re-vectorization trig split for generic `wpAt`. -/
lemma reVec3_wpAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
    reVec3 (wpAt m s p)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (p : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (p : ℝ)) • reVec3 (ws s) := by
  funext i
  simp [reVec3, wpAt, Complex.add_re, Pi.add_apply, Pi.smul_apply,
        add_assoc, add_comm, add_left_comm, mul_assoc]
  ring_nf

/-- Re-vectorization trig split for `wp2At`. -/
lemma reVec3_wp2At (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    reVec3 (wp2At m s)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (ws s) := by
  simpa [wp2At] using (reVec3_wpAt (m := m) (s := s) (p := 2))

/-- Re-vectorization trig split for `wp3At`. -/
lemma reVec3_wp3At (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    reVec3 (wp3At m s)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (ws s) := by
  simpa [wp3At] using (reVec3_wpAt (m := m) (s := s) (p := 3))

/-- The generic trig-split determinant identity: only the `b`-component survives. -/
lemma ell_of_trigSplit
    (u0 uc us : Fin 3 → ℝ) (a b : ℝ) :
    ell u0 uc (u0 + a • uc + b • us) = b * kappa u0 uc us := by
  classical
  calc
    ell u0 uc (u0 + a • uc + b • us)
        = ell u0 uc (u0 + a • uc) + ell u0 uc (b • us) := by
            simpa [add_assoc] using (ell_add u0 uc (u0 + a • uc) (b • us))
    _ = (ell u0 uc u0 + ell u0 uc (a • uc)) + b * ell u0 uc us := by
            simp [ell_add, ell_smul, add_assoc]
    _ = b * kappa u0 uc us := by
          have hu0 : ell u0 uc u0 = 0 := by
            simpa using (ell_u0 (u0 := u0) (uc := uc))
          have huc : ell u0 uc (a • uc) = 0 := by
            simp [ell_smul, ell_uc]
          simp [hu0, huc, ell_us_eq_kappa]

/-- Generic determinant identity: `ell(..., wpAt p)` equals `bCoeff(p) * kappa`. -/
lemma ell_wpAt_eq_b_mul_kappa (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p))
      =
    bCoeff (σ s) (t s) (p : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  calc
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p))
        =
      ell (reVec3 (w0At m s)) (reVec3 (wc s))
        (reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) (p : ℝ)) • reVec3 (wc s)
          + (bCoeff (σ s) (t s) (p : ℝ)) • reVec3 (ws s)) := by
            simp [reVec3_wpAt]
    _ =
      bCoeff (σ s) (t s) (p : ℝ)
        * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using
            (ell_of_trigSplit
              (u0 := reVec3 (w0At m s))
              (uc := reVec3 (wc s))
              (us := reVec3 (ws s))
              (a := aCoeff (σ s) (t s) (p : ℝ))
              (b := bCoeff (σ s) (t s) (p : ℝ)))

/-- Determinant identity: `ell(..., wp2At)` equals `bCoeff * kappa`. -/
lemma ell_wp2At_eq_b_mul_kappa (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
      =
    bCoeff (σ s) (t s) (2 : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  simpa [wp2At] using (ell_wpAt_eq_b_mul_kappa (m := m) (s := s) (p := 2))

/-- Determinant identity: `ell(..., wp3At)` equals `bCoeff * kappa`. -/
lemma ell_wp3At_eq_b_mul_kappa (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
      =
    bCoeff (σ s) (t s) (3 : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  simpa [wp3At] using (ell_wpAt_eq_b_mul_kappa (m := m) (s := s) (p := 3))

/-- The “AtOrder” Lemma-C core package: (hb2,hb3) plus κ≠0 (Option A widened). -/
structure XiLemmaC_CoreAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop where
  hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0
  hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0
  hkappaAt : (kappaAt m s ≠ 0) ∨ (kappaAtIm m s ≠ 0)

/-- Core ⇒ `ell(..., wp2At)=0`. -/
theorem XiLemmaC_hell2At_of_core (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (h : XiLemmaC_CoreAt m s) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 := by
  calc
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
        =
      bCoeff (σ s) (t s) (2 : ℝ)
        * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using (ell_wp2At_eq_b_mul_kappa (m := m) (s := s))
    _ = 0 := by simpa [h.hb2]

/-- Core ⇒ `ell(..., wp3At)=0`. -/
theorem XiLemmaC_hell3At_of_core (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (h : XiLemmaC_CoreAt m s) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0 := by
  calc
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
        =
      bCoeff (σ s) (t s) (3 : ℝ)
        * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using (ell_wp3At_eq_b_mul_kappa (m := m) (s := s))
    _ = 0 := by simpa [h.hb3]

/-- JetPivot κ-leverage (Re): `Re(Ξ^{(m)}(sc)) ≠ 0` ⇒ `Or.inl (kappaAt≠0)`. -/
theorem hkappaAt_of_cderivRe_ne0 (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hRe : (((cderivIter m Xi) (sc s))).re ≠ 0) :
    (kappaAt m s ≠ 0) ∨ (kappaAtIm m s ≠ 0) := by
  refine Or.inl ?_
  intro hk0
  apply hRe
  have hk1 : kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
    simpa [kappaAt] using hk0
  simpa using (by
    have hk2 := hk1
    rw [XiLemmaC_kappa_closedFormAt (m := m) (s := s)] at hk2
    exact hk2)

/-- JetPivot κ-leverage (Im): `Im(Ξ^{(m)}(sc)) ≠ 0` ⇒ `Or.inr (kappaAtIm≠0)`. -/
theorem hkappaAt_of_cderivIm_ne0 (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hIm : (((cderivIter m Xi) (sc s))).im ≠ 0) :
    (kappaAt m s ≠ 0) ∨ (kappaAtIm m s ≠ 0) := by
  refine Or.inr ?_
  intro hk0
  apply hIm
  have hk1 : kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
    simpa [kappaAtIm] using hk0
  simpa using (by
    have hk2 := hk1
    rw [XiLemmaC_kappa_closedFormAt_im (m := m) (s := s)] at hk2
    exact hk2)

end XiPacket
end Targets
end Hyperlocal
