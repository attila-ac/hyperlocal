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

/-- The product of the “other three” factors at `ρ`, i.e. without `(s-ρ)^k`.

We parenthesize as `a * (b * c)` so that
`(analyticAt a).mul ((analyticAt b).mul (analyticAt c))`
matches directly without extra reassociation. -/
def W_at_rho (ρ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  (s - star ρ) ^ k * ((s - Hyperlocal.oneMinus ρ) ^ k * (s - Hyperlocal.oneMinus (star ρ)) ^ k)

/-- Factorization of the denominator near `ρ`: `(Rρk ρ k).eval s = (s-ρ)^k * W_at_rho ρ k s`. -/
lemma R_eval_eq_at_rho (ρ : ℂ) (k : ℕ) (s : ℂ) :
    (Hyperlocal.Factorization.Rρk ρ k).eval s
  = (s - ρ) ^ k * W_at_rho ρ k s := by
  classical
  -- Expand to the 4-factor evaluation and reassociate into the chosen `W_at_rho` shape.
  simp [Hyperlocal.Factorization.Rρk,
        Hyperlocal.MinimalModel.quartetPolyPow,
        Hyperlocal.MinimalModel.lin, Hyperlocal.MinimalModel.linPow,
        eval_pow, eval_sub, eval_X, eval_C,
        W_at_rho, mul_comm, mul_left_comm, mul_assoc]

/-- `W_at_rho` is analytic at `ρ`. -/
lemma W_at_rho_analytic (ρ : ℂ) (k : ℕ) :
  AnalyticAt ℂ (fun s => W_at_rho ρ k s) ρ := by
  -- Each factor is analytic, and we deliberately chose parentheses to match `mul`.
  have a1 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - Hyperlocal.oneMinus ρ) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - Hyperlocal.oneMinus (star ρ)) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  -- Exactly `a1.mul (a2.mul a3)` matches `W_at_rho`'s parentheses.
  simpa [W_at_rho] using a1.mul (a2.mul a3)

/-- Under the usual three separations at `ρ`, `W_at_rho ρ k ρ ≠ 0`. -/
lemma W_at_rho_ne_zero_at_rho
  {ρ : ℂ} {k : ℕ}
  (h1 : ρ ≠ star ρ)
  (h2 : ρ ≠ Hyperlocal.oneMinus ρ)
  (h3 : ρ ≠ Hyperlocal.oneMinus (star ρ)) :
  W_at_rho ρ k ρ ≠ 0 := by
  have nz1 : (ρ - star ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h1)
  have nz2 : (ρ - Hyperlocal.oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h2)
  have nz3 : (ρ - Hyperlocal.oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h3)
  -- Build the triple product in the same parentheses as `W_at_rho`.
  have : (ρ - star ρ) ^ k * ((ρ - Hyperlocal.oneMinus ρ) ^ k * (ρ - Hyperlocal.oneMinus (star ρ)) ^ k) ≠ 0 :=
    mul_ne_zero nz1 (mul_ne_zero nz2 nz3)
  simpa [W_at_rho] using this

/--
### Removable singularity at `z = ρ`

Assume:
* `hfac`: global factorization `H s = (Rρk ρ k).eval s * G s`,
* local factorization at `ρ`: `H s = (s - ρ)^k * J s` with `J` analytic at `ρ`,
* the three separations ensuring `W_at_rho ρ k ρ ≠ 0`,
* and the actual value `G ρ = J ρ / W_at_rho ρ k ρ`.

Then `G` is analytic at `ρ`.
-/
theorem G_analytic_at_rho_of_value
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (J : ℂ → ℂ) (J_an : AnalyticAt ℂ J ρ)
  (H_eq : ∀ s, H s = (s - ρ)^k * J s)
  (h1 : ρ ≠ star ρ) (h2 : ρ ≠ oneMinus ρ) (h3 : ρ ≠ oneMinus (star ρ))
  (hGval : G ρ = J ρ / W_at_rho ρ k ρ) :
  AnalyticAt ℂ G ρ := by
  classical
  -- Denominator factoring: R.eval = (s-ρ)^k * W, with W analytic and W(ρ) ≠ 0.
  have R_eq := R_eval_eq_at_rho ρ k
  have W_an := W_at_rho_analytic ρ k
  have W_ne0 := W_at_rho_ne_zero_at_rho (k := k) h1 h2 h3

  -- Analytic extension `F := J / W`.
  let F : ℂ → ℂ := fun s => J s / W_at_rho ρ k s
  have F_an : AnalyticAt ℂ F ρ := J_an.div W_an W_ne0

  -- Show G = F on a neighborhood of ρ.
  have h_eq : G =ᶠ[nhds ρ] F := by
    have hW₀ : ∀ᶠ s in nhds ρ, W_at_rho ρ k s ≠ 0 :=
      W_an.continuousAt.eventually_ne W_ne0
    refine hW₀.mono ?_
    intro s hWs
    by_cases hsρ : s = ρ
    · subst hsρ
      -- At the center, use the provided removable value.
      simp [F, hGval]
    · -- Off the center: cancel (s-ρ)^k safely.
      have hpow : (s - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hsρ)
      -- From hfac, H_eq, and R_eq:
      have hfac_eq := hfac s
      have hH : H s = (s - ρ)^k * J s := H_eq s
      have hR : (Hyperlocal.Factorization.Rρk ρ k).eval s
                = (s - ρ) ^ k * W_at_rho ρ k s := R_eq s
      -- Rearrange to `(s-ρ)^k * J s = (s-ρ)^k * (W * G s)`
      have step₁ :
        (s - ρ)^k * J s = ((s - ρ)^k * W_at_rho ρ k s) * G s := by
        simpa [hH, hR, mul_assoc, mul_comm, mul_left_comm] using hfac_eq
      have step₂ :
        (s - ρ)^k * J s = (s - ρ)^k * (W_at_rho ρ k s * G s) := by
        -- reassociate `((a*b)*c) = a*(b*c)`
        simpa [mul_assoc] using step₁
      -- Cancel `(s-ρ)^k` and solve for `J s`.
      have J_eq : J s = W_at_rho ρ k s * G s :=
        (mul_left_cancel₀ hpow) step₂
      -- Feed exactly `G s * W = J s` to `eq_div_iff_mul_eq`.
      have needed : G s * W_at_rho ρ k s = J s := by
        -- rewrite `J s` using `J_eq`, then commute the product
        simpa [J_eq, mul_comm]
      exact (eq_div_iff_mul_eq hWs).mpr needed

  -- Transport analyticity along eventual equality.
  exact F_an.congr h_eq.symm

end FactorizationAnalytic
end Hyperlocal
