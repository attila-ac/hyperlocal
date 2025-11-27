/-
  FactorizationGofSEntire.lean
  Glue the off-quartet analyticity with the four removable points
  to conclude: G is entire.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization
import Hyperlocal.FactorizationGofSAnalytic
import Hyperlocal.FactorizationGofSNonVanishing
import Hyperlocal.Removable

noncomputable section
open Complex
open scoped Topology

namespace Hyperlocal
namespace FactorizationGofSEntire

/--
`G` is entire once we know:
* the global factorization holds at **each** quartet base (`ρ`, `star ρ`, `1-ρ`, `1-star ρ`);
* `H` is entire;
* local data at each quartet point giving the removable value.

We use:
* off-quartet analyticity (`FactorizationAnalytic.G_analytic_off_quartet`);
* the removable lemma at a quartet point (`FactorizationAnalytic.G_analytic_at_rho_of_value`).
-/
theorem entire_G_of_factorisation
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  -- global factorization at each quartet anchor
  (hfacρ     : Factorization.FactorisedByQuartet H ρ k G)
  (hfacρ'    : Factorization.FactorisedByQuartet H (star ρ) k G)
  (hfac1mρ   : Factorization.FactorisedByQuartet H (oneMinus ρ) k G)
  (hfac1mρ'  : Factorization.FactorisedByQuartet H (oneMinus (star ρ)) k G)
  -- H is entire
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
  -- local expansions and removable values at each quartet point
  (locρ :
    ∃ J, AnalyticAt ℂ J ρ ∧ (∀ s, H s = (s - ρ)^k * J s) ∧
          ρ ≠ star ρ ∧ ρ ≠ oneMinus ρ ∧ ρ ≠ oneMinus (star ρ) ∧
          G ρ = J ρ / FactorizationAnalytic.W_at_rho ρ k ρ)
  (locρ' :
    ∃ J', AnalyticAt ℂ J' (star ρ) ∧ (∀ s, H s = (s - star ρ)^k * J' s) ∧
           star ρ ≠ ρ ∧ star ρ ≠ oneMinus ρ ∧ star ρ ≠ oneMinus (star ρ) ∧
           G (star ρ) = J' (star ρ) / FactorizationAnalytic.W_at_rho (star ρ) k (star ρ))
  (loc1mρ :
    ∃ J₂, AnalyticAt ℂ J₂ (oneMinus ρ) ∧ (∀ s, H s = (s - oneMinus ρ)^k * J₂ s) ∧
           oneMinus ρ ≠ ρ ∧ oneMinus ρ ≠ star ρ ∧ oneMinus ρ ≠ oneMinus (star ρ) ∧
           G (oneMinus ρ) = J₂ (oneMinus ρ) / FactorizationAnalytic.W_at_rho (oneMinus ρ) k (oneMinus ρ))
  (loc1mρ' :
    ∃ J₃, AnalyticAt ℂ J₃ (oneMinus (star ρ)) ∧
           (∀ s, H s = (s - oneMinus (star ρ))^k * J₃ s) ∧
           oneMinus (star ρ) ≠ ρ ∧ oneMinus (star ρ) ≠ star ρ ∧
           oneMinus (star ρ) ≠ oneMinus ρ ∧
           G (oneMinus (star ρ)) = J₃ (oneMinus (star ρ)) / FactorizationAnalytic.W_at_rho (oneMinus (star ρ)) k (oneMinus (star ρ))) :
  ∀ z : ℂ, AnalyticAt ℂ G z := by
  intro z
  -- Split: either z is off the quartet or it is one of the four points
  have split :
    (z ≠ ρ ∧ z ≠ star ρ ∧ z ≠ oneMinus ρ ∧ z ≠ oneMinus (star ρ))
    ∨ z = ρ ∨ z = star ρ ∨ z = oneMinus ρ ∨ z = oneMinus (star ρ) := by
    by_cases hz : z = ρ
    · exact Or.inr (Or.inl hz)
    by_cases hz' : z = star ρ
    · exact Or.inr (Or.inr (Or.inl hz'))
    by_cases h1 : z = oneMinus ρ
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    by_cases h2 : z = oneMinus (star ρ)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h2)))
    · exact Or.inl ⟨by simpa using hz, by simpa using hz', by simpa using h1, by simpa using h2⟩

  rcases split with hOff | r
  · -- Off the quartet: use your proven lemma
    rcases hOff with ⟨hz, hz', h1, h2⟩
    exact Hyperlocal.FactorizationAnalytic.G_analytic_off_quartet
      hfacρ H_an (by simpa using hz) (by simpa using hz') (by simpa using h1) (by simpa using h2)

  -- On the quartet: use the removable lemma at the appropriate point
  rcases r with hz | r
  · rcases locρ with ⟨J, J_an, H_eq, a1, a2, a3, gval⟩
    -- NOTE: Removable lemma **does not** take H_an in your current version
    simpa [hz] using
      Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
        hfacρ J J_an H_eq a1 a2 a3 gval

  rcases r with hz' | r
  · rcases locρ' with ⟨J', J'_an, H_eq', b1, b2, b3, gval'⟩
    simpa [hz'] using
      Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
        hfacρ' J' J'_an H_eq' b1 b2 b3 gval'

  rcases r with h1 | h2
  · rcases loc1mρ with ⟨J₂, J₂_an, H_eq₂, c1, c2, c3, gval₂⟩
    simpa [h1] using
      Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
        hfac1mρ J₂ J₂_an H_eq₂ c1 c2 c3 gval₂
  · rcases loc1mρ' with ⟨J₃, J₃_an, H_eq₃, d1, d2, d3, gval₃⟩
    simpa [h2] using
      Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
        hfac1mρ' J₃ J₃_an H_eq₃ d1 d2 d3 gval₃

/-! ### Center = star ρ ---------------------------------------------------- -/

/-- The “other three” product when the center is `a = star ρ`. -/
def W_conj (ρ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((s - ρ) ^ k) * ((s - oneMinus ρ) ^ k) * ((s - oneMinus (star ρ)) ^ k)

/-- Isolate `(s - star ρ)^k` from `(Rρk ρ k).eval s`. -/
lemma R_eval_isolate_conj (ρ : ℂ) (k : ℕ) (s : ℂ) :
  (Hyperlocal.Factorization.Rρk ρ k).eval s
    = (s - star ρ) ^ k * W_conj ρ k s := by
  -- same algebra as the ρ-case, just regroup factors
  simpa [W_conj, mul_comm, mul_left_comm, mul_assoc]
    using Hyperlocal.FactorizationAnalytic.eval_Rρk_explicit ρ s k

/-- Analyticity of `W_conj` at `star ρ`. -/
lemma W_conj_analytic (ρ : ℂ) (k : ℕ) :
  AnalyticAt ℂ (fun s => W_conj ρ k s) (star ρ) := by
  have a1 : AnalyticAt ℂ (fun s => (s - ρ) ^ k) (star ρ) :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - oneMinus ρ) ^ k) (star ρ) :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - oneMinus (star ρ)) ^ k) (star ρ) :=
    (analyticAt_id.sub analyticAt_const).pow k
  simpa [W_conj, mul_comm, mul_left_comm, mul_assoc] using a1.mul (a2.mul a3)

/-- Nonvanishing of `W_conj` at the center under the three separations there. -/
lemma W_conj_ne0_at_conj
  {ρ : ℂ} {k : ℕ}
  (h1 : star ρ ≠ ρ) (h2 : star ρ ≠ oneMinus ρ) (h3 : star ρ ≠ oneMinus (star ρ)) :
  W_conj ρ k (star ρ) ≠ 0 := by
  have nz1 : ((star ρ) - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h1)
  have nz2 : ((star ρ) - oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h2)
  have nz3 : ((star ρ) - oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h3)
  have : ((star ρ) - ρ) ^ k * ((star ρ) - oneMinus ρ) ^ k * ((star ρ) - oneMinus (star ρ)) ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero nz1 nz2) nz3
  simpa [W_conj, mul_comm, mul_left_comm, mul_assoc]

/-- Analyticity of `G` at `star ρ` from local data there. -/
lemma G_analytic_at_conj
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (J : ℂ → ℂ) (J_an : AnalyticAt ℂ J (star ρ))
  (H_eq : ∀ s, H s = (s - star ρ)^k * J s)
  (h1 : star ρ ≠ ρ) (h2 : star ρ ≠ oneMinus ρ) (h3 : star ρ ≠ oneMinus (star ρ))
  (gval : G (star ρ) = J (star ρ) / W_conj ρ k (star ρ)) :
  AnalyticAt ℂ G (star ρ) := by
  have W_an  : AnalyticAt ℂ (fun s => W_conj ρ k s) (star ρ) := W_conj_analytic ρ k
  have W_ne0 : W_conj ρ k (star ρ) ≠ 0 := W_conj_ne0_at_conj (k := k) h1 h2 h3
  exact
    G_analytic_at_center hfac
      (W := fun s => W_conj ρ k s)
      (R_eq := R_eval_isolate_conj ρ k)
      W_an W_ne0
      J J_an H_eq gval


/-! ### Center = 1 - ρ ----------------------------------------------------- -/

/-- The “other three” product when the center is `a = 1 - ρ`. -/
def W_1mρ (ρ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((s - ρ) ^ k) * ((s - star ρ) ^ k) * ((s - oneMinus (star ρ)) ^ k)

/-- Isolate `(s - (1-ρ))^k` from `(Rρk ρ k).eval s`. -/
lemma R_eval_isolate_1mρ (ρ : ℂ) (k : ℕ) (s : ℂ) :
  (Hyperlocal.Factorization.Rρk ρ k).eval s
    = (s - oneMinus ρ) ^ k * W_1mρ ρ k s := by
  simpa [W_1mρ, mul_comm, mul_left_comm, mul_assoc]
    using Hyperlocal.FactorizationAnalytic.eval_Rρk_explicit ρ s k

lemma W_1mρ_analytic (ρ : ℂ) (k : ℕ) :
  AnalyticAt ℂ (fun s => W_1mρ ρ k s) (oneMinus ρ) := by
  have a1 : AnalyticAt ℂ (fun s => (s - ρ) ^ k) (oneMinus ρ) :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) (oneMinus ρ) :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - oneMinus (star ρ)) ^ k) (oneMinus ρ) :=
    (analyticAt_id.sub analyticAt_const).pow k
  simpa [W_1mρ, mul_comm, mul_left_comm, mul_assoc] using a1.mul (a2.mul a3)

lemma W_1mρ_ne0_at_1mρ
  {ρ : ℂ} {k : ℕ}
  (h1 : oneMinus ρ ≠ ρ) (h2 : oneMinus ρ ≠ star ρ) (h3 : oneMinus ρ ≠ oneMinus (star ρ)) :
  W_1mρ ρ k (oneMinus ρ) ≠ 0 := by
  have nz1 : ((oneMinus ρ) - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h1)
  have nz2 : ((oneMinus ρ) - star ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h2)
  have nz3 : ((oneMinus ρ) - oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h3)
  have : ((oneMinus ρ) - ρ) ^ k *
          ((oneMinus ρ) - star ρ) ^ k *
          ((oneMinus ρ) - oneMinus (star ρ)) ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero nz1 nz2) nz3
  simpa [W_1mρ, mul_comm, mul_left_comm, mul_assoc]

lemma G_analytic_at_1mρ
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (J : ℂ → ℂ) (J_an : AnalyticAt ℂ J (oneMinus ρ))
  (H_eq : ∀ s, H s = (s - oneMinus ρ)^k * J s)
  (h1 : oneMinus ρ ≠ ρ) (h2 : oneMinus ρ ≠ star ρ) (h3 : oneMinus ρ ≠ oneMinus (star ρ))
  (gval : G (oneMinus ρ) = J (oneMinus ρ) / W_1mρ ρ k (oneMinus ρ)) :
  AnalyticAt ℂ G (oneMinus ρ) := by
  have W_an  : AnalyticAt ℂ (fun s => W_1mρ ρ k s) (oneMinus ρ) := W_1mρ_analytic ρ k
  have W_ne0 : W_1mρ ρ k (oneMinus ρ) ≠ 0 := W_1mρ_ne0_at_1mρ (k := k) h1 h2 h3
  exact
    G_analytic_at_center hfac
      (W := fun s => W_1mρ ρ k s)
      (R_eq := R_eval_isolate_1mρ ρ k)
      W_an W_ne0
      J J_an H_eq gval


/-! ### Center = 1 - star ρ ------------------------------------------------ -/

/-- The “other three” product when the center is `a = 1 - star ρ`. -/
def W_1mρ' (ρ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ((s - ρ) ^ k) * ((s - star ρ) ^ k) * ((s - oneMinus ρ) ^ k)

/-- Isolate `(s - (1 - star ρ))^k` from `(Rρk ρ k).eval s`. -/
lemma R_eval_isolate_1mρ' (ρ : ℂ) (k : ℕ) (s : ℂ) :
  (Hyperlocal.Factorization.Rρk ρ k).eval s
    = (s - oneMinus (star ρ)) ^ k * W_1mρ' ρ k s := by
  simpa [W_1mρ', mul_comm, mul_left_comm, mul_assoc]
    using Hyperlocal.FactorizationAnalytic.eval_Rρk_explicit ρ s k

lemma W_1mρ'_analytic (ρ : ℂ) (k : ℕ) :
  AnalyticAt ℂ (fun s => W_1mρ' ρ k s) (oneMinus (star ρ)) := by
  have a1 : AnalyticAt ℂ (fun s => (s - ρ) ^ k) (oneMinus (star ρ)) :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) (oneMinus (star ρ)) :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - oneMinus ρ) ^ k) (oneMinus (star ρ)) :=
    (analyticAt_id.sub analyticAt_const).pow k
  simpa [W_1mρ', mul_comm, mul_left_comm, mul_assoc] using a1.mul (a2.mul a3)

lemma W_1mρ'_ne0_at_1mρ'
  {ρ : ℂ} {k : ℕ}
  (h1 : oneMinus (star ρ) ≠ ρ)
  (h2 : oneMinus (star ρ) ≠ star ρ)
  (h3 : oneMinus (star ρ) ≠ oneMinus ρ) :
  W_1mρ' ρ k (oneMinus (star ρ)) ≠ 0 := by
  have nz1 : ((oneMinus (star ρ)) - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h1)
  have nz2 : ((oneMinus (star ρ)) - star ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h2)
  have nz3 : ((oneMinus (star ρ)) - oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h3)
  have : ((oneMinus (star ρ)) - ρ) ^ k *
          ((oneMinus (star ρ)) - star ρ) ^ k *
          ((oneMinus (star ρ)) - oneMinus ρ) ^ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero nz1 nz2) nz3
  simpa [W_1mρ', mul_comm, mul_left_comm, mul_assoc]

lemma G_analytic_at_1mρ'
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (J : ℂ → ℂ) (J_an : AnalyticAt ℂ J (oneMinus (star ρ)))
  (H_eq : ∀ s, H s = (s - oneMinus (star ρ))^k * J s)
  (h1 : oneMinus (star ρ) ≠ ρ)
  (h2 : oneMinus (star ρ) ≠ star ρ)
  (h3 : oneMinus (star ρ) ≠ oneMinus ρ)
  (gval : G (oneMinus (star ρ)) = J (oneMinus (star ρ)) / W_1mρ' ρ k (oneMinus (star ρ))) :
  AnalyticAt ℂ G (oneMinus (star ρ)) := by
  have W_an  : AnalyticAt ℂ (fun s => W_1mρ' ρ k s) (oneMinus (star ρ)) := W_1mρ'_analytic ρ k
  have W_ne0 : W_1mρ' ρ k (oneMinus (star ρ)) ≠ 0 := W_1mρ'_ne0_at_1mρ' (k := k) h1 h2 h3
  exact
    G_analytic_at_center hfac
      (W := fun s => W_1mρ' ρ k s)
      (R_eq := R_eval_isolate_1mρ' ρ k)
      W_an W_ne0
      J J_an H_eq gval


end FactorizationGofSEntire
end Hyperlocal
