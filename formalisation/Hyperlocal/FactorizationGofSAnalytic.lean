import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Basic

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization

noncomputable section
open Complex Polynomial
open scoped BigOperators

namespace Hyperlocal
namespace FactorizationAnalytic

/-- Local evaluation: `(X - z)^k` at `s` is `(s - z)^k`. -/
@[simp] lemma eval_linPow_local (s z : ℂ) (k : ℕ) :
    (MinimalModel.linPow z k).eval s = (s - z) ^ k := by
  simp [MinimalModel.lin, MinimalModel.linPow]

/-- Expand `(Rρk ρ k).eval s` into four explicit factors (a convenient parenthesization). -/
lemma eval_Rρk_explicit (ρ s : ℂ) (k : ℕ) :
    (Factorization.Rρk ρ k).eval s
      = (s - ρ) ^ k *
        ((s - star ρ) ^ k *
        ((s - oneMinus ρ) ^ k *
         (s - oneMinus (star ρ)) ^ k)) := by
  simp [Factorization.Rρk, MinimalModel.quartetPolyPow,
        MinimalModel.lin, MinimalModel.linPow,
        eval_pow, eval_sub, eval_X, eval_C,
        mul_comm, mul_left_comm, mul_assoc]

/-- Outside the quartet, `(Rρk ρ k).eval z ≠ 0`. No need to split on `k=0`. -/
lemma eval_Rρk_ne_zero_off
    (ρ z : ℂ) (k : ℕ)
    (hz1 : z ≠ ρ) (hz2 : z ≠ star ρ) (hz3 : z ≠ oneMinus ρ) (hz4 : z ≠ oneMinus (star ρ)) :
    (Factorization.Rρk ρ k).eval z ≠ 0 := by
  -- Each base factor is nonzero; hence every power is nonzero for all k (including k = 0).
  have nz1  : z - ρ ≠ 0 := sub_ne_zero.mpr hz1
  have nz2  : z - star ρ ≠ 0 := sub_ne_zero.mpr hz2
  have nz3  : z - oneMinus ρ ≠ 0 := sub_ne_zero.mpr hz3
  have nz4  : z - oneMinus (star ρ) ≠ 0 := sub_ne_zero.mpr hz4
  have nzp1 : (z - ρ) ^ k ≠ 0 := pow_ne_zero _ nz1
  have nzp2 : (z - star ρ) ^ k ≠ 0 := pow_ne_zero _ nz2
  have nzp3 : (z - oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ nz3
  have nzp4 : (z - oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ nz4
  -- Work with a flat product first.
  have hprod_flat :
      (z - ρ) ^ k *
      (z - star ρ) ^ k *
      (z - oneMinus ρ) ^ k *
      (z - oneMinus (star ρ)) ^ k ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_ne_zero (mul_ne_zero nzp1 nzp2) (mul_ne_zero nzp3 nzp4))
  -- Convert to the explicit parenthesization we stated above.
  have : (Factorization.Rρk ρ k).eval z
        = (z - ρ) ^ k *
          ((z - star ρ) ^ k *
          ((z - oneMinus ρ) ^ k *
           (z - oneMinus (star ρ)) ^ k)) := eval_Rρk_explicit ρ z k
  -- Conclude nonvanishing.
  simpa [this, mul_comm, mul_left_comm, mul_assoc] using hprod_flat

/-- `R(s) := (Rρk ρ k).eval s` is analytic everywhere (by explicit 4-factor expansion). -/
lemma analyticAt_eval_Rρk_as_product (ρ : ℂ) (k : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun s => (Factorization.Rρk ρ k).eval s) z := by
  -- Each factor `s ↦ (s - c)^k` is analytic.
  have a1 : AnalyticAt ℂ (fun s => (s - ρ) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - oneMinus ρ) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a4 : AnalyticAt ℂ (fun s => (s - oneMinus (star ρ)) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  -- Multiply them together and reassociate.
  have a12 : AnalyticAt ℂ (fun s => (s - ρ) ^ k * (s - star ρ) ^ k) z := a1.mul a2
  have a34 : AnalyticAt ℂ (fun s => (s - oneMinus ρ) ^ k * (s - oneMinus (star ρ)) ^ k) z := a3.mul a4
  have a1234 :
      AnalyticAt ℂ
        (fun s =>
          ((s - ρ) ^ k * (s - star ρ) ^ k) *
          ((s - oneMinus ρ) ^ k * (s - oneMinus (star ρ)) ^ k)) z := a12.mul a34
  have : AnalyticAt ℂ
      (fun s =>
        (s - ρ) ^ k *
        (s - star ρ) ^ k *
        (s - oneMinus ρ) ^ k *
        (s - oneMinus (star ρ)) ^ k) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using a1234
  -- Match the explicit evaluation form.
  simpa [eval_Rρk_explicit, mul_comm, mul_left_comm, mul_assoc]

/-- Off the quartet, `G` is analytic. -/
theorem G_analytic_off_quartet
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Factorization.FactorisedByQuartet H ρ k G)
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z) :
  ∀ ⦃z : ℂ⦄,
    z ≠ ρ → z ≠ star ρ → z ≠ oneMinus ρ → z ≠ oneMinus (star ρ) →
    AnalyticAt ℂ G z := by
  classical
  intro z hz1 hz2 hz3 hz4
  set R : ℂ[X] := Factorization.Rρk ρ k
  -- denominator nonzero
  have nzR : R.eval z ≠ 0 := eval_Rρk_ne_zero_off ρ z k hz1 hz2 hz3 hz4
  -- analyticity of numerator and denominator
  have H_at : AnalyticAt ℂ H z := H_an z
  have R_at : AnalyticAt ℂ (fun s => R.eval s) z :=
    analyticAt_eval_Rρk_as_product ρ k z
  -- The quotient `F s := H s / R.eval s` is analytic at `z`.
  have F_at : AnalyticAt ℂ (fun s => H s / R.eval s) z :=
    H_at.div R_at nzR
  -- local equality of G with H/R near z
  have eventually_ne : ∀ᶠ s in nhds z, R.eval s ≠ 0 :=
    R_at.continuousAt.eventually_ne nzR
  have h_loc : G =ᶠ[nhds z] (fun s => H s / R.eval s) := by
    refine eventually_ne.mono ?_
    intro w hw
    -- hfac w : H w = R.eval w * G w
    -- We want: G w = H w / R.eval w
    -- Use the field lemma `eq_div_iff_mul_eq`.
    exact (eq_div_iff_mul_eq hw).mpr (by simpa [mul_comm] using (hfac w).symm)
  -- conclude by congruence of germs
  exact F_at.congr h_loc.symm

end FactorizationAnalytic
end Hyperlocal

end section
