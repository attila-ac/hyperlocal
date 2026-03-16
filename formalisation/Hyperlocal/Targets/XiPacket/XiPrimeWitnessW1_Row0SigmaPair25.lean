import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Hyperlocal.Cancellation.LogFiveDivTwoLogThreeDivTwoNotRat
import Hyperlocal.Cancellation.TwoPrimePhaseLockCore
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_GenericPrime
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_RouteARecurrenceAtOneSubRhoFromWcSigma
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiWindowJetPivot_wpAtExpand
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket
open Hyperlocal.Cancellation
open JetPivot

namespace W1

/-- `log(5/2) = log 5 - log 2`. -/
lemma log_five_div_two :
    Real.log ((5 : ℝ) / (2 : ℝ)) = Real.log (5 : ℝ) - Real.log (2 : ℝ) := by
  have h5 : (5 : ℝ) ≠ 0 := by norm_num
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  simpa using (Real.log_div h5 h2)

/-- The real 2×2 determinant for the pair `{2,5}`. -/
def det25R (σ t : ℝ) : ℝ :=
  aCoeff σ t (2 : ℝ) * bCoeff σ t (5 : ℝ)
    - aCoeff σ t (5 : ℝ) * bCoeff σ t (2 : ℝ)

/--
Closed form:
  det25R(σ,t) = pSigma σ 2 * pSigma σ 5 * sin(t*log(5/2)).
-/
theorem det25R_eq_pSigma_mul_sin_log_ratio (σ t : ℝ) :
    det25R σ t
      =
    (pSigma σ (2 : ℝ)) * (pSigma σ (5 : ℝ)) *
      Real.sin (t * Real.log ((5 : ℝ) / (2 : ℝ))) := by
  classical
  unfold det25R aCoeff bCoeff

  have hfactor :
      pSigma σ (2 : ℝ) * Real.cos (t * Real.log (2 : ℝ)) *
            (pSigma σ (5 : ℝ) * Real.sin (t * Real.log (5 : ℝ)))
        -
      pSigma σ (5 : ℝ) * Real.cos (t * Real.log (5 : ℝ)) *
            (pSigma σ (2 : ℝ) * Real.sin (t * Real.log (2 : ℝ)))
        =
      (pSigma σ (2 : ℝ) * pSigma σ (5 : ℝ)) *
        (Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (5 : ℝ))
          - Real.cos (t * Real.log (5 : ℝ)) * Real.sin (t * Real.log (2 : ℝ))) := by
    ring

  have htrig :
      (Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (5 : ℝ))
        - Real.cos (t * Real.log (5 : ℝ)) * Real.sin (t * Real.log (2 : ℝ)))
        =
      Real.sin (t * Real.log (5 : ℝ) - t * Real.log (2 : ℝ)) := by
    have h := Real.sin_sub (t * Real.log (5 : ℝ)) (t * Real.log (2 : ℝ))
    have :
        Real.sin (t * Real.log (5 : ℝ) - t * Real.log (2 : ℝ))
          =
        Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (5 : ℝ))
          - Real.cos (t * Real.log (5 : ℝ)) * Real.sin (t * Real.log (2 : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact this.symm

  have hlog :
      t * Real.log (5 : ℝ) - t * Real.log (2 : ℝ)
        =
      t * Real.log ((5 : ℝ) / (2 : ℝ)) := by
    calc
      t * Real.log (5 : ℝ) - t * Real.log (2 : ℝ)
          = t * (Real.log (5 : ℝ) - Real.log (2 : ℝ)) := by ring
      _ = t * Real.log ((5 : ℝ) / (2 : ℝ)) := by
            simpa using congrArg (fun x => t * x) (log_five_div_two).symm

  calc
    pSigma σ (2 : ℝ) * Real.cos (t * Real.log (2 : ℝ)) *
          (pSigma σ (5 : ℝ) * Real.sin (t * Real.log (5 : ℝ)))
      -
    pSigma σ (5 : ℝ) * Real.cos (t * Real.log (5 : ℝ)) *
          (pSigma σ (2 : ℝ) * Real.sin (t * Real.log (2 : ℝ)))
        =
      (pSigma σ (2 : ℝ) * pSigma σ (5 : ℝ)) *
        (Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (5 : ℝ))
          - Real.cos (t * Real.log (5 : ℝ)) * Real.sin (t * Real.log (2 : ℝ))) := by
      simpa using hfactor
  _ =
      (pSigma σ (2 : ℝ) * pSigma σ (5 : ℝ)) *
        Real.sin (t * Real.log (5 : ℝ) - t * Real.log (2 : ℝ)) := by
      simp [htrig]
  _ =
      (pSigma σ (2 : ℝ) * pSigma σ (5 : ℝ)) *
        Real.sin (t * Real.log ((5 : ℝ) / (2 : ℝ))) := by
      simp [hlog]
  _ =
      (pSigma σ (2 : ℝ)) * (pSigma σ (5 : ℝ)) *
        Real.sin (t * Real.log ((5 : ℝ) / (2 : ℝ))) := by
      ring

/-- Complex-cast nonvanishing for the pair `{2,5}`. -/
theorem det25C_ne_zero_of_tval_ne_zero
    (σ t : ℝ)
    (htv :
      ((Real.sin (t * Real.log ((5 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    (aCoeff σ t (2 : ℝ) : ℂ) * (bCoeff σ t (5 : ℝ) : ℂ)
      -
    (aCoeff σ t (5 : ℝ) : ℂ) * (bCoeff σ t (2 : ℝ) : ℂ) ≠ 0 := by
  have hsin : Real.sin (t * Real.log ((5 : ℝ) / (2 : ℝ))) ≠ 0 := by
    intro h0
    apply htv
    simpa [h0]
  have hp2 : pSigma σ (2 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (2 : ℝ)))
  have hp5 : pSigma σ (5 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (5 : ℝ)))
  have hR : det25R σ t ≠ 0 := by
    have hprod :
        (pSigma σ (2 : ℝ)) * (pSigma σ (5 : ℝ)) *
          Real.sin (t * Real.log ((5 : ℝ) / (2 : ℝ))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hp2 hp5) hsin
    simpa [det25R_eq_pSigma_mul_sin_log_ratio (σ := σ) (t := t)] using hprod
  intro hC
  have hC' : ((det25R σ t : ℝ) : ℂ) = 0 := by
    simpa [det25R] using hC
  have hR0 : det25R σ t = 0 := by
    exact_mod_cast hC'
  exact hR hR0

@[simp] lemma row0Sigma_add
    (s : OffSeed Xi) (w u : Transport.Window 3) :
    row0Sigma s (w + u) = row0Sigma s w + row0Sigma s u := by
  simp [row0Sigma, add_mul, mul_add, add_assoc, add_left_comm, add_comm]

@[simp] lemma row0Sigma_smul
    (s : OffSeed Xi) (a : ℂ) (w : Transport.Window 3) :
    row0Sigma s (a • w) = a * row0Sigma s w := by
  simp [row0Sigma]
  ring

/--
The pair `{2,5}` row-0 linear algebra only needs one extra local input beyond
the canonical `w0/wp2` row-0 zeroes: namely the row-0 zero for `wpAt ... 5`.

This isolates the exact remaining generic-prime burden.
-/
theorem row0Sigma_wc_eq_zero_of_tval25_ne_zero_of_row0_wp5
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hwp5 : row0Sigma s (wpAt 0 s 5) = 0)
    (htv :
      ((Real.sin ((t s) * Real.log ((5 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    row0Sigma s (wc s) = 0 := by
  let A2 : ℂ := (aCoeff (σ s) (t s) (2 : ℝ) : ℂ)
  let B2 : ℂ := (bCoeff (σ s) (t s) (2 : ℝ) : ℂ)
  let A5 : ℂ := (aCoeff (σ s) (t s) (5 : ℝ) : ℂ)
  let B5 : ℂ := (bCoeff (σ s) (t s) (5 : ℝ) : ℂ)

  let x : ℂ := row0Sigma s (wc s)
  let y : ℂ := row0Sigma s (ws s)

  have hw0 : row0Sigma s (w0At 0 s) = 0 := sigma_w0At (m := 0) (s := s)
  have hwp2 : row0Sigma s (wp2At 0 s) = 0 := sigma_wp2At (m := 0) (s := s)

  have hwp2exp :
      wp2At 0 s = w0At 0 s + A2 • wc s + B2 • ws s := by
    funext i
    simp [wp2At_apply, A2, B2]
    ring_nf

  have hwp5exp :
      wpAt 0 s 5 = w0At 0 s + A5 • wc s + B5 • ws s := by
    funext i
    simp [wpAt_apply, A5, B5]
    ring_nf

  have eq2_aux :
      row0Sigma s (w0At 0 s) + (A2 * x + B2 * y) = 0 := by
    have hwp2_zero :
        row0Sigma s (w0At 0 s + A2 • wc s + B2 • ws s) = 0 := by
      simpa [hwp2exp] using hwp2
    rw [row0Sigma_add, row0Sigma_add, row0Sigma_smul, row0Sigma_smul] at hwp2_zero
    convert hwp2_zero using 1 <;> simp only [x, y] <;> ring

  have eq5_aux :
      row0Sigma s (w0At 0 s) + (A5 * x + B5 * y) = 0 := by
    have hwp5_zero :
        row0Sigma s (w0At 0 s + A5 • wc s + B5 • ws s) = 0 := by
      simpa [hwp5exp] using hwp5
    rw [row0Sigma_add, row0Sigma_add, row0Sigma_smul, row0Sigma_smul] at hwp5_zero
    convert hwp5_zero using 1 <;> simp only [x, y] <;> ring

  have eq2 : A2 * x + B2 * y = 0 := by
    have h := eq2_aux
    rw [hw0, zero_add] at h
    exact h

  have eq5 : A5 * x + B5 * y = 0 := by
    have h := eq5_aux
    rw [hw0, zero_add] at h
    exact h

  have hdet : A2 * B5 - A5 * B2 ≠ 0 := by
    simpa [A2, B2, A5, B5, sub_eq_add_neg] using
      (det25C_ne_zero_of_tval_ne_zero (σ := σ s) (t := t s) htv)

  have hxmul : (A2 * B5 - A5 * B2) * x = 0 := by
    calc
      (A2 * B5 - A5 * B2) * x
          = B5 * (A2 * x + B2 * y) - B2 * (A5 * x + B5 * y) := by
              ring
      _ = 0 := by simp [eq2, eq5]

  have hx0 : x = 0 := (mul_eq_zero.mp hxmul).resolve_left hdet
  simpa [x] using hx0

/--
Class-based wrapper: the previous theorem is discharged once the generic-prime
row-0 zero for `wpAt ... 5` is available.
-/
theorem row0Sigma_wc_eq_zero_of_tval25_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((5 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    row0Sigma s (wc s) = 0 := by
  have hwp5 : row0Sigma s (wpAt 0 s 5) = 0 := by
    rw [← toeplitzL_row0_eq_row0Sigma (s := s) (w := wpAt 0 s 5)]
    exact xiJetQuot_row0_wpAt_of_trueAnalyticPrime (m := 0) (s := s) (p := 5)
  exact row0Sigma_wc_eq_zero_of_tval25_ne_zero_of_row0_wp5
    (s := s) (hwp5 := hwp5) (htv := htv)

/--
On the exact `log(3/2)`-resonant branch, the pair `{2,5}` is automatically
nonresonant. Therefore any resonant-branch proof of

  row0Sigma s (wpAt 0 s 5) = 0

already closes the preferred seam `(A)`.
-/
theorem row0Sigma_wc_eq_zero_of_resonant32_of_row0_wp5
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hwp5 : row0Sigma s (wpAt 0 s 5) = 0) :
    row0Sigma s (wc s) = 0 := by
  have ht0 : t s ≠ 0 := by
    simpa [XiPacket.t] using s.ht

  have hsin25 : Real.sin ((t s) * Real.log ((5 : ℝ) / (2 : ℝ))) ≠ 0 := by
    intro h25
    rcases Hyperlocal.Cancellation.PrimeWitness.sin_eq_int_mul_pi
      (x := (t s) * Real.log ((3 : ℝ) / (2 : ℝ))) hres with ⟨m, hm⟩
    rcases Hyperlocal.Cancellation.PrimeWitness.sin_eq_int_mul_pi
      (x := (t s) * Real.log ((5 : ℝ) / (2 : ℝ))) h25 with ⟨n, hn⟩

    have hm0 : m ≠ 0 := by
      intro hm0
      have htm : (t s) * Real.log ((3 : ℝ) / (2 : ℝ)) = 0 := by
        simpa [hm0] using hm
      have hlog32 : Real.log ((3 : ℝ) / (2 : ℝ)) ≠ 0 := by
        have hpos : (0 : ℝ) < Real.log ((3 : ℝ) / (2 : ℝ)) := by
          simpa using Real.log_pos (by norm_num : (1 : ℝ) < ((3 : ℝ) / (2 : ℝ)))
        exact ne_of_gt hpos
      exact ht0 ((mul_eq_zero.mp htm).resolve_right hlog32)

    have hrat :
        Real.log ((5 : ℝ) / (2 : ℝ)) / Real.log ((3 : ℝ) / (2 : ℝ))
          =
        (n : ℝ) / (m : ℝ) := by
      have hm' : Real.log ((3 : ℝ) / (2 : ℝ)) = ((m : ℝ) * Real.pi) / (t s) := by
        have := congrArg (fun x => x / (t s)) hm
        simp [mul_div_cancel_left₀, ht0] at this
        exact this

      have hn' : Real.log ((5 : ℝ) / (2 : ℝ)) = ((n : ℝ) * Real.pi) / (t s) := by
        have := congrArg (fun x => x / (t s)) hn
        simp [mul_div_cancel_left₀, ht0] at this
        exact this

      have hm_neR : (m : ℝ) ≠ 0 := by
        exact Int.cast_ne_zero.mpr hm0

      calc
        Real.log ((5 : ℝ) / (2 : ℝ)) / Real.log ((3 : ℝ) / (2 : ℝ))
            =
          ((((n : ℝ) * Real.pi) / (t s)) / (((m : ℝ) * Real.pi) / (t s))) := by
            simp [hm', hn']
        _ = (n : ℝ) / (m : ℝ) := by
            field_simp [Real.pi_ne_zero, ht0, hm_neR]
            ring

    exact Hyperlocal.Cancellation.PrimeWitness.log52_log32_notRat
      ⟨n, m, hm0, hrat⟩

  have htv25 :
      ((Real.sin ((t s) * Real.log ((5 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hsin25

  exact row0Sigma_wc_eq_zero_of_tval25_ne_zero_of_row0_wp5
    (s := s) (hwp5 := hwp5) (htv := htv25)

/--
Class-based wrapper of the previous resonant-branch theorem.
-/
theorem row0Sigma_wc_eq_zero_of_resonant32
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0) :
    row0Sigma s (wc s) = 0 := by
  have hwp5 : row0Sigma s (wpAt 0 s 5) = 0 := by
    rw [← toeplitzL_row0_eq_row0Sigma (s := s) (w := wpAt 0 s 5)]
    exact xiJetQuot_row0_wpAt_of_trueAnalyticPrime (m := 0) (s := s) (p := 5)
  exact row0Sigma_wc_eq_zero_of_resonant32_of_row0_wp5
    (s := s) (hres := hres) (hwp5 := hwp5)

/--
Route–A recurrence on the exact resonant branch, obtained via the second pair
`{2,5}` and the clean seam `(A)`.
-/
theorem routeA_recurrence_at_one_sub_rho_of_resonant32
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0) :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  exact routeA_recurrence_at_one_sub_rho_of_row0Sigma_wc
    (s := s)
    (hsigma := row0Sigma_wc_eq_zero_of_resonant32 (s := s) (hres := hres))

@[simp] lemma row0Sigma_ws_closed
    (s : OffSeed Xi) :
    row0Sigma s (ws s) = (-(2 : ℂ)) := by
  simp [row0Sigma, ws_eq_basis, basisW3, e2]

@[simp] lemma row0Sigma_wc_closed
    (s : OffSeed Xi) :
    row0Sigma s (wc s)
      = (JetQuotOp.σ2 s : ℂ) - (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  simp [row0Sigma, wc_eq_basis, basisW3, e1, e2]
  ring

theorem row0Sigma_wpAt5_closed_form
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (wpAt 0 s 5)
      =
    ((aCoeff (σ s) (t s) (5 : ℝ) : ℂ) * row0Sigma s (wc s))
      - (2 : ℂ) * (bCoeff (σ s) (t s) (5 : ℝ)) := by
  have hw0At : row0Sigma s (w0At 0 s) = 0 := sigma_w0At (m := 0) (s := s)
  have hw0 : row0Sigma s (w0 s) = 0 := by
    simpa [w0At_zero_fromWcStencil (s := s)] using hw0At

  have hwp5exp :
      wpAt 0 s 5
        =
      w0 s
        + ((aCoeff (σ s) (t s) (5 : ℝ) : ℂ)) • wc s
        + ((bCoeff (σ s) (t s) (5 : ℝ) : ℂ)) • ws s := by
    funext i
    simp [wpAt, w0At_zero_fromWcStencil (s := s)]
    ring_nf

  calc
    row0Sigma s (wpAt 0 s 5)
        =
      row0Sigma s
        (w0 s
          + ((aCoeff (σ s) (t s) (5 : ℝ) : ℂ)) • wc s
          + ((bCoeff (σ s) (t s) (5 : ℝ) : ℂ)) • ws s) := by
            simpa [hwp5exp]
    _ =
      row0Sigma s (w0 s)
        + (((aCoeff (σ s) (t s) (5 : ℝ) : ℂ) * row0Sigma s (wc s))
          + ((bCoeff (σ s) (t s) (5 : ℝ) : ℂ) * row0Sigma s (ws s))) := by
            rw [row0Sigma_add, row0Sigma_add, row0Sigma_smul, row0Sigma_smul]
            ring_nf
    _ =
      ((aCoeff (σ s) (t s) (5 : ℝ) : ℂ) * row0Sigma s (wc s))
        + ((bCoeff (σ s) (t s) (5 : ℝ) : ℂ) * row0Sigma s (ws s)) := by
            simp [hw0]
    _ =
      ((aCoeff (σ s) (t s) (5 : ℝ) : ℂ) * row0Sigma s (wc s))
        - (2 : ℂ) * (bCoeff (σ s) (t s) (5 : ℝ)) := by
            have hws : row0Sigma s (ws s) = (-(2 : ℂ)) :=
              row0Sigma_ws_closed (s := s)
            rw [hws]
            ring

theorem row0Sigma_wpAt5_eq_zero_of_row0Sigma_wc_zero_and_bCoeff5_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hsigma : row0Sigma s (wc s) = 0)
    (hb5 : bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    row0Sigma s (wpAt 0 s 5) = 0 := by
  rw [row0Sigma_wpAt5_closed_form, hsigma, hb5]
  simp

theorem row0Sigma_wpAt5_eq_zero_of_sigma2_eq_two_delta_and_bCoeff5_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5 : bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    row0Sigma s (wpAt 0 s 5) = 0 := by
  apply row0Sigma_wpAt5_eq_zero_of_row0Sigma_wc_zero_and_bCoeff5_zero
  · exact row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta (s := s) (hσ2δ := hσ2δ)
  · exact hb5
end W1

end XiPacket
end Targets
end Hyperlocal
