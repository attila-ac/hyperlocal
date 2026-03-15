/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_RecurrenceToEllKappaAtOrder_GenericPrime.lean

  First genuine W1-facing generic-prime export over the actual family `wpAt m s p`.

  Provides:
    * generic trig split for `reVec3 (wpAt m s p)`
    * generic determinant identity
        ell(..., reVec3 (wpAt m s p)) = bCoeff(..., p) * kappa(...)
    * generic elimination:
        if the real-pivot ell-out at `wpAt m s p` vanishes and `kappaAt m s ≠ 0`,
        then `bCoeff(..., p) = 0`

  Pure finite-dimensional algebra. No new axioms.
-/

import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Generic real-part trig split for the actual prime family `wpAt`. -/
lemma reVec3_wpAt
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
    reVec3 (wpAt m s p)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (p : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (p : ℝ)) • reVec3 (ws s) := by
  funext i
  simp [reVec3, wpAt, Complex.add_re, Pi.add_apply, Pi.smul_apply,
        add_assoc, add_comm, add_left_comm, mul_assoc]
  ring_nf

/--
Generic determinant identity on the real pivot:
the `ell` witness of the actual prime window is exactly `bCoeff * kappa`.
-/
lemma ell_wpAt_eq_b_mul_kappa
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
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
            simpa [reVec3_wpAt]
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

/--
Generic real-pivot elimination:
once an arbitrary-prime ell-out theorem is available, this converts it immediately into
`bCoeff(..., p) = 0`.
-/
theorem bCoeff_eq_zero_of_ell_wpAt_zero
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    (hk : kappaAt m s ≠ 0)
    (hell :
      ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  have hmul :
      bCoeff (σ s) (t s) (p : ℝ) *
          kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
    rw [ell_wpAt_eq_b_mul_kappa (m := m) (s := s) (p := p)] at hell
    exact hell

  have hmul' : bCoeff (σ s) (t s) (p : ℝ) * kappaAt m s = 0 := by
    simpa [kappaAt, mul_assoc] using hmul

  exact (mul_eq_zero.mp hmul').resolve_right hk

/-- The old `{2,3}` exports are immediate specialisations of the genuine generic-prime ones. -/
lemma reVec3_wp2At_from_generic
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    reVec3 (wp2At m s)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (ws s) := by
  simpa [wp2At] using reVec3_wpAt (m := m) (s := s) (p := 2)

lemma reVec3_wp3At_from_generic
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    reVec3 (wp3At m s)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (ws s) := by
  simpa [wp3At] using reVec3_wpAt (m := m) (s := s) (p := 3)

lemma ell_wp2At_eq_b_mul_kappa_from_generic
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
      =
    bCoeff (σ s) (t s) (2 : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  simpa [wp2At] using ell_wpAt_eq_b_mul_kappa (m := m) (s := s) (p := 2)

lemma ell_wp3At_eq_b_mul_kappa_from_generic
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
      =
    bCoeff (σ s) (t s) (3 : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  simpa [wp3At] using ell_wpAt_eq_b_mul_kappa (m := m) (s := s) (p := 3)

end XiPacket
end Targets
end Hyperlocal
