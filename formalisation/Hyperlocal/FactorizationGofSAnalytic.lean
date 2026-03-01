import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Basic

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization

noncomputable section
open Complex Polynomial
open scoped BigOperators Topology

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
  have nz1  : z - ρ ≠ 0 := sub_ne_zero.mpr hz1
  have nz2  : z - star ρ ≠ 0 := sub_ne_zero.mpr hz2
  have nz3  : z - oneMinus ρ ≠ 0 := sub_ne_zero.mpr hz3
  have nz4  : z - oneMinus (star ρ) ≠ 0 := sub_ne_zero.mpr hz4
  have nzp1 : (z - ρ) ^ k ≠ 0 := pow_ne_zero _ nz1
  have nzp2 : (z - star ρ) ^ k ≠ 0 := pow_ne_zero _ nz2
  have nzp3 : (z - oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ nz3
  have nzp4 : (z - oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ nz4
  have hprod_flat :
      (z - ρ) ^ k *
      (z - star ρ) ^ k *
      (z - oneMinus ρ) ^ k *
      (z - oneMinus (star ρ)) ^ k ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_ne_zero (mul_ne_zero nzp1 nzp2) (mul_ne_zero nzp3 nzp4))
  have : (Factorization.Rρk ρ k).eval z
        = (z - ρ) ^ k *
          ((z - star ρ) ^ k *
          ((z - oneMinus ρ) ^ k *
           (z - oneMinus (star ρ)) ^ k)) := eval_Rρk_explicit ρ z k
  simpa [this, mul_comm, mul_left_comm, mul_assoc] using hprod_flat

/-- `R(s) := (Rρk ρ k).eval s` is analytic everywhere (by explicit 4-factor expansion). -/
lemma analyticAt_eval_Rρk_as_product (ρ : ℂ) (k : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun s => (Factorization.Rρk ρ k).eval s) z := by
  have a1 : AnalyticAt ℂ (fun s => (s - ρ) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - oneMinus ρ) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a4 : AnalyticAt ℂ (fun s => (s - oneMinus (star ρ)) ^ k) z :=
    (analyticAt_id.sub analyticAt_const).pow k
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
  simpa [eval_Rρk_explicit, mul_comm, mul_left_comm, mul_assoc] using this

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
  have nzR : R.eval z ≠ 0 := eval_Rρk_ne_zero_off ρ z k hz1 hz2 hz3 hz4
  have H_at : AnalyticAt ℂ H z := H_an z
  have R_at : AnalyticAt ℂ (fun s => R.eval s) z :=
    analyticAt_eval_Rρk_as_product ρ k z
  have F_at : AnalyticAt ℂ (fun s => H s / R.eval s) z :=
    H_at.div R_at nzR
  have eventually_ne : ∀ᶠ s in nhds z, R.eval s ≠ 0 :=
    R_at.continuousAt.eventually_ne nzR
  have h_loc : G =ᶠ[nhds z] (fun s => H s / R.eval s) := by
    refine eventually_ne.mono ?_
    intro w hw
    exact (eq_div_iff_mul_eq hw).mpr (by simpa [mul_comm] using (hfac w).symm)
  exact F_at.congr h_loc.symm

/-! ---------------------------------------------------------------------------
Removable singularity upgrade (at ρ)

IMPORTANT: kept in a SUBNAMESPACE to avoid name collisions with `Hyperlocal.Removable`.
---------------------------------------------------------------------------- -/

namespace RemAtRho

/-- The product of the “other three” factors at `ρ`, i.e. without `(s-ρ)^k`. -/
def W_at_rho (ρ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  (s - star ρ) ^ k * ((s - oneMinus ρ) ^ k * (s - oneMinus (star ρ)) ^ k)

/-- Factorization near `ρ`: `(Rρk ρ k).eval s = (s-ρ)^k * W_at_rho ρ k s`. -/
lemma R_eval_eq_at_rho (ρ : ℂ) (k : ℕ) (s : ℂ) :
    (Factorization.Rρk ρ k).eval s
  = (s - ρ) ^ k * W_at_rho ρ k s := by
  classical
  simpa [W_at_rho, mul_assoc] using (eval_Rρk_explicit ρ s k)

/-- `W_at_rho` is analytic at `ρ`. -/
lemma W_at_rho_analytic (ρ : ℂ) (k : ℕ) :
  AnalyticAt ℂ (fun s => W_at_rho ρ k s) ρ := by
  have a1 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - oneMinus ρ) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - oneMinus (star ρ)) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  simpa [W_at_rho] using a1.mul (a2.mul a3)

/-- Under the usual three separations at `ρ`, `W_at_rho ρ k ρ ≠ 0`. -/
lemma W_at_rho_ne_zero_at_rho
  {ρ : ℂ} {k : ℕ}
  (h1 : ρ ≠ star ρ)
  (h2 : ρ ≠ oneMinus ρ)
  (h3 : ρ ≠ oneMinus (star ρ)) :
  W_at_rho ρ k ρ ≠ 0 := by
  have nz1 : (ρ - star ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h1)
  have nz2 : (ρ - oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h2)
  have nz3 : (ρ - oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h3)
  have : (ρ - star ρ) ^ k * ((ρ - oneMinus ρ) ^ k * (ρ - oneMinus (star ρ)) ^ k) ≠ 0 :=
    mul_ne_zero nz1 (mul_ne_zero nz2 nz3)
  simpa [W_at_rho] using this

/--
Removable singularity at `ρ` (local upgrade).

Same statement as yours, but names live under `RemAtRho.*` so they don't collide globally.
-/
theorem G_analytic_at_rho_of_value
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Factorization.FactorisedByQuartet H ρ k G)
  (J : ℂ → ℂ) (J_an : AnalyticAt ℂ J ρ)
  (H_eq : ∀ s, H s = (s - ρ)^k * J s)
  (h1 : ρ ≠ star ρ) (h2 : ρ ≠ oneMinus ρ) (h3 : ρ ≠ oneMinus (star ρ))
  (hGval : G ρ = J ρ / W_at_rho ρ k ρ) :
  AnalyticAt ℂ G ρ := by
  classical

  have R_eq := R_eval_eq_at_rho ρ k
  have W_an := W_at_rho_analytic ρ k
  have W_ne0 := W_at_rho_ne_zero_at_rho (k := k) h1 h2 h3

  let F : ℂ → ℂ := fun s => J s / W_at_rho ρ k s
  have F_an : AnalyticAt ℂ F ρ := J_an.div W_an W_ne0

  have h_eq : G =ᶠ[nhds ρ] F := by
    have hW₀ : ∀ᶠ s in nhds ρ, W_at_rho ρ k s ≠ 0 :=
      W_an.continuousAt.eventually_ne W_ne0
    refine hW₀.mono ?_
    intro s hWs
    by_cases hsρ : s = ρ
    · subst hsρ
      simp [F, hGval]
    ·
      have hpow : (s - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hsρ)

      have hfac_eq := hfac s
      have hH : H s = (s - ρ)^k * J s := H_eq s
      have hR : (Factorization.Rρk ρ k).eval s
                = (s - ρ) ^ k * W_at_rho ρ k s := R_eq s

      have step₁ :
        (s - ρ)^k * J s = ((s - ρ)^k * W_at_rho ρ k s) * G s := by
        simpa [hH, hR, mul_assoc, mul_comm, mul_left_comm] using hfac_eq

      have step₂ :
        (s - ρ)^k * J s = (s - ρ)^k * (W_at_rho ρ k s * G s) := by
        simpa [mul_assoc] using step₁

      -- cancel (s-ρ)^k, order-robust
      have J_eq : J s = W_at_rho ρ k s * G s := by
        have h := (mul_eq_mul_left_iff).1 step₂
        cases h with
        | inl h₁ =>
            -- either equality or zero-case; handle both robustly
            -- If h₁ is the equality, `exact h₁` works; if it is the zero-case, contradiction closes it.
            first
              | exact h₁
              | exfalso; exact hpow h₁
        | inr h₂ =>
            first
              | exact h₂
              | exfalso; exact hpow h₂

      have needed : G s * W_at_rho ρ k s = J s := by
        simpa [J_eq, mul_comm, mul_left_comm, mul_assoc]

      exact (eq_div_iff_mul_eq hWs).mpr needed

  exact F_an.congr h_eq.symm

end RemAtRho

end FactorizationAnalytic
end Hyperlocal
