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

  This file ALSO exports small plumbing helpers:
    • `cderivIter_ne0_of_dslopeIter_ne0`
    • `cderivIter_re_ne0_or_im_ne0_of_dslopeIter_ne0`
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

/--
dslope-iterate at the anchor equals `(deriv^[m] Xi)(sc) / m!`.

NOTE: this lemma is intentionally **not private** (used by downstream plumbing).
-/
lemma dslopeIter_eq_derivIter_div_factorial
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
      -- κ=0 ⇒ Re(cderivIter)=0 via closed form.
      have hRe_cderiv0 : ((cderivIter m Xi) (sc s)).re = 0 := by
        calc
          ((cderivIter m Xi) (sc s)).re
              =
            kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
              simpa using (XiLemmaC_kappa_closedFormAt (m := m) (s := s)).symm
          _ = 0 := hk

      -- hence Re(deriv^[m])=0 (since `cderivIter` is definitional iterate of `deriv`)
      have hRe_deriv0 : (((deriv^[m] Xi) (sc s))).re = 0 := by
        simpa [cderivIter] using hRe_cderiv0

      -- dslope = deriv / m!
      have hds :
          dslopeIterAt (m := m) (s := s)
            =
          ((deriv^[m] Xi) (sc s)) / (Nat.factorial m : ℂ) :=
        dslopeIter_eq_derivIter_div_factorial (m := m) (s := s)

      -- Take real parts; RHS has real-part 0, so dslope.re = 0, contradiction.
      have : (dslopeIterAt (m := m) (s := s)).re = 0 := by
        -- from hds, rewrite and use hRe_deriv0
        -- `simp` handles real part of division by real scalar
        have hfacC : (Nat.factorial m : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero m)
        -- rewrite as mul by inv
        simp [hds, div_eq_mul_inv, hRe_deriv0, hfacC]  -- yields dslope.re = 0
      exact hRe this

  | inr hIm =>
      refine Or.inr ?_
      intro hk
      -- κ=0 ⇒ Im(cderivIter)=0 via closed form.
      have hIm_cderiv0 : ((cderivIter m Xi) (sc s)).im = 0 := by
        calc
          ((cderivIter m Xi) (sc s)).im
              =
            kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
              simpa using (XiLemmaC_kappa_closedFormAt_im (m := m) (s := s)).symm
          _ = 0 := hk

      have hIm_deriv0 : (((deriv^[m] Xi) (sc s))).im = 0 := by
        simpa [cderivIter] using hIm_cderiv0

      have hds :
          dslopeIterAt (m := m) (s := s)
            =
          ((deriv^[m] Xi) (sc s)) / (Nat.factorial m : ℂ) :=
        dslopeIter_eq_derivIter_div_factorial (m := m) (s := s)

      have : (dslopeIterAt (m := m) (s := s)).im = 0 := by
        have hfacC : (Nat.factorial m : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero m)
        simp [hds, div_eq_mul_inv, hIm_deriv0, hfacC]
      exact hIm this

/-!
## Plumbing helpers (AXIOM-FREE)

These let downstream “jet-language” files continue to work without resurrecting the old shim.
-/

/-- dslope witness ⇒ nonzero complex jet entry at the same order. -/
theorem cderivIter_ne0_of_dslopeIter_ne0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hmDs : dslopeIterAt (m := m) (s := s) ≠ 0) :
    (cderivIter m Xi (sc s)) ≠ (0 : ℂ) := by
  intro h0
  -- convert to deriv-iterate form
  have hderiv0 : (deriv^[m] Xi) (sc s) = 0 := by
    simpa [cderivIter] using h0
  -- then dslopeIterAt = 0 by the dslope/deriv identity, contradiction
  have hds :
      dslopeIterAt (m := m) (s := s)
        =
      ((deriv^[m] Xi) (sc s)) / (Nat.factorial m : ℂ) :=
    dslopeIter_eq_derivIter_div_factorial (m := m) (s := s)
  apply hmDs
  simp [hds, hderiv0]

/-- dslope witness ⇒ (Re ≠ 0) ∨ (Im ≠ 0) at the same order (jet language). -/
theorem cderivIter_re_ne0_or_im_ne0_of_dslopeIter_ne0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hmDs : dslopeIterAt (m := m) (s := s) ≠ 0) :
    (((cderivIter m Xi) (sc s)).re ≠ 0) ∨ (((cderivIter m Xi) (sc s)).im ≠ 0) := by
  have hjet : (cderivIter m Xi (sc s)) ≠ (0 : ℂ) :=
    cderivIter_ne0_of_dslopeIter_ne0 (m := m) (s := s) hmDs
  by_contra h
  push_neg at h
  exact hjet (Complex.ext h.1 h.2)

end XiPacket
end Targets
end Hyperlocal
