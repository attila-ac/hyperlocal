/-
  Hyperlocal/Targets/XiPacket/XiDslopeToKappaAtOrder.lean

  Plan C++J bridge (dslope → κ-gate), snapshot-robust.

  Input: dslope-nonflatness witness
      ((Function.swap dslope (sc s))^[m] Xi) (sc s) ≠ 0

  Output: κ-gate (Or-shape):
      (kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0).

  IMPORTANT:
  We do NOT rely on any `hkappaAt_of_cderiv(Re|Im)_ne0` lemma.
  We use ONLY:
    • the κ closed forms from `XiWindowKappaClosedFormAtOrder`,
    • the dslope→deriv/factorial identity (proved here),
    • elementary Re/Im splitting.
-/

import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder
import Hyperlocal.Targets.XiPacket.XiJetNonflatOfAnalytic

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Topology
open scoped Real
open FormalMultilinearSeries
open Hyperlocal.Transport

/-- Local alias: the dslope-iterate used by `xiJetNonflat_dslope_exists`. -/
abbrev dslopeIterAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : ℂ :=
  ((Function.swap dslope (sc s))^[m] Xi) (sc s)

/-- dslope-iterate at the anchor equals `(deriv^[m] Xi)(sc) / m!` (your snapshot route). -/
private lemma dslopeIter_eq_derivIter_div_factorial
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    dslopeIterAt (m := m) (s := s)
      =
    ((deriv^[m] Xi) (sc s)) / (Nat.factorial m : ℂ) := by
  classical
  let z0 : ℂ := sc s

  -- Analyticity at z0 (project lemma).
  have hAna : AnalyticAt ℂ Xi z0 := by
    simpa [z0] using (Xi_entire (z := z0))

  -- Canonical 1D series: ofScalars (iteratedDeriv / n!)
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n Xi z0 / n.factorial)

  have hpAt : HasFPowerSeriesAt Xi p z0 := by
    simpa [p] using
      (AnalyticAt.hasFPowerSeriesAt (𝕜 := ℂ) (f := Xi) (x := z0) hAna)

  -- dslope iterate corresponds to fslope iterate on the series.
  have hpIter :
      HasFPowerSeriesAt ((Function.swap dslope z0)^[m] Xi)
        ((FormalMultilinearSeries.fslope^[m]) p) z0 :=
    HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope
      (f := Xi) (p := p) (z₀ := z0) (n := m) hpAt

  have h0 :
      (FormalMultilinearSeries.fslope^[m] p).coeff 0
        =
      ((Function.swap dslope z0)^[m] Xi) z0 := by
    simpa using (hpIter.coeff_zero 1)

  have hcoeff :
      (FormalMultilinearSeries.fslope^[m] p).coeff 0 = p.coeff m := by
    simpa using (FormalMultilinearSeries.coeff_iterate_fslope (p := p) (n := m))

  have hpcoeff :
      p.coeff m = (iteratedDeriv m Xi z0) / (Nat.factorial m : ℂ) := by
    simp [p, FormalMultilinearSeries.coeff_ofScalars]

  have hds :
      dslopeIterAt (m := m) (s := s)
        =
      (iteratedDeriv m Xi z0) / (Nat.factorial m : ℂ) := by
    have :
        ((Function.swap dslope z0)^[m] Xi) z0
          =
        (iteratedDeriv m Xi z0) / (Nat.factorial m : ℂ) := by
      calc
        ((Function.swap dslope z0)^[m] Xi) z0
            = (FormalMultilinearSeries.fslope^[m] p).coeff 0 := by
                simpa [h0]
        _   = p.coeff m := hcoeff
        _   = (iteratedDeriv m Xi z0) / (Nat.factorial m : ℂ) := hpcoeff
    simpa [dslopeIterAt, z0] using this

  -- iteratedDeriv = iterate deriv (in 1D)
  simpa [iteratedDeriv_eq_iterate, z0] using hds

/-- Main deliverable: dslope witness ⇒ κ-gate (Or-shape). -/
theorem hkappaAt_of_dslopeIter_ne0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hmDs : dslopeIterAt (m := m) (s := s) ≠ 0) :
    (kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
      ∨
    (kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) := by
  have hParts :
      (dslopeIterAt (m := m) (s := s)).re ≠ 0 ∨ (dslopeIterAt (m := m) (s := s)).im ≠ 0 := by
    by_contra h
    push_neg at h
    exact hmDs (Complex.ext h.1 h.2)

  cases hParts with
  | inl hRe =>
      refine Or.inl ?_
      intro hk
      -- Put `hk` into the exact `(wc s)/(ws s)` shape (in case simp unfolded them).
      have hkT :
          kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
        simpa [wc_eq_basis, ws_eq_basis] using hk

      -- κ=0 ⇒ Re(cderivIter)=0 via the closed form.
      have hRe_cderiv0 : ((cderivIter m Xi) (sc s)).re = 0 := by
        calc
          ((cderivIter m Xi) (sc s)).re
              =
            kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
              simpa using (XiLemmaC_kappa_closedFormAt (m := m) (s := s)).symm
          _ = 0 := hkT

      -- Turn this into a statement about `(deriv^[m] Xi)`.
      have hRe_deriv0 : (((deriv^[m] Xi) (sc s))).re = 0 := by
        simpa [cderivIter] using hRe_cderiv0

      -- dslope = deriv / m!
      have hds :
          dslopeIterAt (m := m) (s := s)
            =
          ((deriv^[m] Xi) (sc s)) / (Nat.factorial m : ℂ) :=
        dslopeIter_eq_derivIter_div_factorial (m := m) (s := s)

      -- Multiply by factorial in ℂ: ds * fac = deriv
      have hmul :
          dslopeIterAt (m := m) (s := s) * (Nat.factorial m : ℂ)
            =
          ((deriv^[m] Xi) (sc s)) := by
        have hfacC : (Nat.factorial m : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero m)
        have := congrArg (fun z ↦ z * (Nat.factorial m : ℂ)) hds
        simpa [div_eq_mul_inv, mul_assoc, hfacC] using this

      -- Take real parts: ds.re * fac = 0 (since deriv.re = 0)
      have hmul_re0 : (dslopeIterAt (m := m) (s := s)).re * (Nat.factorial m : ℝ) = 0 := by
        have := congrArg Complex.re hmul
        -- RHS becomes 0 using hRe_deriv0; LHS simplifies since factorial is real.
        simpa [hRe_deriv0, Complex.mul_re] using this

      -- Normalize order and cancel factorial.
      have hmul_re0' : (Nat.factorial m : ℝ) * (dslopeIterAt (m := m) (s := s)).re = 0 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_re0

      have hfacR : (Nat.factorial m : ℝ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

      have hRe0 : (dslopeIterAt (m := m) (s := s)).re = 0 := by
        rcases mul_eq_zero.mp hmul_re0' with hfac0 | hds0
        · exact (False.elim (hfacR hfac0))
        · exact hds0

      exact hRe hRe0

  | inr hIm =>
      refine Or.inr ?_
      intro hk
      -- Put `hk` into the exact `(wc s)/(ws s)` shape (in case simp unfolded them).
      have hkT :
          kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
        simpa [wc_eq_basis, ws_eq_basis] using hk

      -- κ=0 ⇒ Im(cderivIter)=0 via the closed form.
      have hIm_cderiv0 : ((cderivIter m Xi) (sc s)).im = 0 := by
        calc
          ((cderivIter m Xi) (sc s)).im
              =
            kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
              simpa using (XiLemmaC_kappa_closedFormAt_im (m := m) (s := s)).symm
          _ = 0 := hkT

      -- Turn this into a statement about `(deriv^[m] Xi)`.
      have hIm_deriv0 : (((deriv^[m] Xi) (sc s))).im = 0 := by
        simpa [cderivIter] using hIm_cderiv0

      -- dslope = deriv / m!
      have hds :
          dslopeIterAt (m := m) (s := s)
            =
          ((deriv^[m] Xi) (sc s)) / (Nat.factorial m : ℂ) :=
        dslopeIter_eq_derivIter_div_factorial (m := m) (s := s)

      -- Multiply by factorial in ℂ: ds * fac = deriv
      have hmul :
          dslopeIterAt (m := m) (s := s) * (Nat.factorial m : ℂ)
            =
          ((deriv^[m] Xi) (sc s)) := by
        have hfacC : (Nat.factorial m : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero m)
        have := congrArg (fun z ↦ z * (Nat.factorial m : ℂ)) hds
        simpa [div_eq_mul_inv, mul_assoc, hfacC] using this

      -- Take imaginary parts: ds.im * fac = 0 (since deriv.im = 0)
      have hmul_im0 : (dslopeIterAt (m := m) (s := s)).im * (Nat.factorial m : ℝ) = 0 := by
        have := congrArg Complex.im hmul
        simpa [hIm_deriv0, Complex.mul_im] using this

      -- Normalize order and cancel factorial.
      have hmul_im0' : (Nat.factorial m : ℝ) * (dslopeIterAt (m := m) (s := s)).im = 0 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_im0

      have hfacR : (Nat.factorial m : ℝ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

      have hIm0 : (dslopeIterAt (m := m) (s := s)).im = 0 := by
        rcases mul_eq_zero.mp hmul_im0' with hfac0 | hds0
        · exact (False.elim (hfacR hfac0))
        · exact hds0

      exact hIm hIm0

end XiPacket
end Targets
end Hyperlocal
