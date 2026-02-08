/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_RecurrenceToEllKappaAtOrder.lean

  Plan C++J (Jet Pivot): “AtOrder” version of the Lemma C core scaffold.

  This file is intentionally cheap + mechanical:
  it duplicates the non-semantic Lemma-C algebra from
  `XiLemmaC_RecurrenceToEllKappa.lean`, but replaces

    w0   ↦ w0At m
    wp2  ↦ wp2At m
    wp3  ↦ wp3At m

  so downstream Stage-4 code can be phrased in terms of definitional jet windows.
-/

import Hyperlocal.Transport.PrimeSineRescue
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

@[simp] lemma re_ofReal_mul (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
  simp [Complex.mul_re]

@[simp] lemma im_ofReal_mul (a : ℝ) (z : ℂ) : ((a : ℂ) * z).im = a * z.im := by
  simp [Complex.mul_im]

/-- Real-part vectorization respects real scalar smul on windows. -/
@[simp] lemma reVec3_smul_ofReal (a : ℝ) (w : Window 3) :
    reVec3 ((a : ℂ) • w) = a • reVec3 w := by
  funext i
  simp [reVec3, Pi.smul_apply]

/-- Re-vectorization trig split for `wp2At`. -/
lemma reVec3_wp2At (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    reVec3 (wp2At m s)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (ws s) := by
  funext i
  -- simp will likely unfold wc/ws into basis form (due to imported simp lemmas),
  -- leaving only a commutative-ring rearrangement.
  simp [reVec3, wp2At, wpAt, Complex.add_re, Pi.add_apply, Pi.smul_apply,
        add_assoc, add_left_comm, add_comm, mul_assoc]
  ring_nf

/-- Re-vectorization trig split for `wp3At`. -/
lemma reVec3_wp3At (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    reVec3 (wp3At m s)
      =
    reVec3 (w0At m s)
      + (aCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (wc s)
      + (bCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (ws s) := by
  funext i
  simp [reVec3, wp3At, wpAt, Complex.add_re, Pi.add_apply, Pi.smul_apply,
        add_assoc, add_left_comm, add_comm, mul_assoc]
  ring_nf

/-- The generic trig-split determinant identity: only the `b`-component survives. -/
lemma ell_of_trigSplit
    (u0 uc us : Fin 3 → ℝ) (a b : ℝ) :
    ell u0 uc (u0 + a • uc + b • us)
      =
    b * kappa u0 uc us := by
  classical
  -- Copy the working proof pattern from `XiLemmaC_RecurrenceToEllKappa.lean`.
  calc
    ell u0 uc (u0 + a • uc + b • us)
        = ell u0 uc (u0 + a • uc) + ell u0 uc (b • us) := by
            simpa [add_assoc] using (ell_add u0 uc (u0 + a • uc) (b • us))
    _ = (ell u0 uc u0 + ell u0 uc (a • uc)) + b * ell u0 uc us := by
            simp [ell_add, ell_smul, add_assoc, add_left_comm, add_comm]
    _ = b * kappa u0 uc us := by
          have hu0 : ell u0 uc u0 = 0 := by
            simpa using (ell_u0 (u0 := u0) (uc := uc))
          have huc : ell u0 uc (a • uc) = 0 := by
            -- multilinearity + repeated column
            simp [ell_smul, ell_uc]
          -- Now the only surviving term is `b * ell u0 uc us`, rewrite it to κ.
          -- (This avoids generating the spurious goal `kappa u0 uc (a • uc) = 0`.)
          simp [hu0, huc, ell_us_eq_kappa, add_assoc, add_left_comm, add_comm]

/-- Determinant identity: `ell(..., wp2At)` equals `bCoeff * kappa`. -/
lemma ell_wp2At_eq_b_mul_kappa (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
      =
    bCoeff (σ s) (t s) (2 : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  calc
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
        =
      ell (reVec3 (w0At m s)) (reVec3 (wc s))
        (reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (wc s)
          + (bCoeff (σ s) (t s) (2 : ℝ)) • reVec3 (ws s)) := by
            simp [reVec3_wp2At]
    _ = bCoeff (σ s) (t s) (2 : ℝ)
          * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using
            (ell_of_trigSplit
              (u0 := reVec3 (w0At m s))
              (uc := reVec3 (wc s))
              (us := reVec3 (ws s))
              (a := aCoeff (σ s) (t s) (2 : ℝ))
              (b := bCoeff (σ s) (t s) (2 : ℝ)))

/-- Determinant identity: `ell(..., wp3At)` equals `bCoeff * kappa`. -/
lemma ell_wp3At_eq_b_mul_kappa (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
      =
    bCoeff (σ s) (t s) (3 : ℝ)
      * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
  calc
    ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
        =
      ell (reVec3 (w0At m s)) (reVec3 (wc s))
        (reVec3 (w0At m s)
          + (aCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (wc s)
          + (bCoeff (σ s) (t s) (3 : ℝ)) • reVec3 (ws s)) := by
            simp [reVec3_wp3At]
    _ = bCoeff (σ s) (t s) (3 : ℝ)
          * kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using
            (ell_of_trigSplit
              (u0 := reVec3 (w0At m s))
              (uc := reVec3 (wc s))
              (us := reVec3 (ws s))
              (a := aCoeff (σ s) (t s) (3 : ℝ))
              (b := bCoeff (σ s) (t s) (3 : ℝ)))

/-- The “AtOrder” Lemma-C core package: (hb2,hb3) plus κ≠0. -/
structure XiLemmaC_CoreAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop where
  hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0
  hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0
  hkappaAt :
    kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0

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

/-- JetPivot leverage: `Re(Ξ^{(m)}(sc)) ≠ 0` ⇒ `κ(m,s) ≠ 0` via closed form. -/
theorem hkappaAt_of_cderivRe_ne0 (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hRe : (((cderivIter m Xi) (sc s))).re ≠ 0) :
    kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
  intro hk
  apply hRe
  have hk' := hk
  -- keep this as `rw`, not `simp`, to avoid rewriting wc/ws into basis forms
  rw [XiLemmaC_kappa_closedFormAt (m := m) (s := s)] at hk'
  exact hk'

end XiPacket
end Targets
end Hyperlocal
