/-
  FactorizationGofSEntire.lean (rho-only stub)
  Minimal step: prove G is analytic at ρ using the removable lemma.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization
import Hyperlocal.FactorizationGofSAnalytic
import Hyperlocal.Removable

noncomputable section
open Complex
open scoped Topology

namespace Hyperlocal
namespace FactorizationGofSEntire

open Hyperlocal.FactorizationAnalytic

/--
Minimal rho-only step toward entirety:

If we have the global factorization at ρ and local data
  `H s = (s - ρ)^k * J s` with `J` analytic at ρ, the three separations at ρ,
  and the value `G ρ = J ρ / W_at_rho ρ k ρ`,
then `G` is analytic at `ρ`.
-/
theorem analytic_at_rho_from_local
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfacρ :
    Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (locρ :
    ∃ J : ℂ → ℂ,
      AnalyticAt ℂ J ρ ∧
      (∀ s, H s = (s - ρ)^k * J s) ∧
      ρ ≠ star ρ ∧
      ρ ≠ Hyperlocal.oneMinus ρ ∧
      ρ ≠ Hyperlocal.oneMinus (star ρ) ∧
      G ρ = J ρ / Hyperlocal.FactorizationAnalytic.W_at_rho ρ k ρ) :
  AnalyticAt ℂ G ρ := by
  rcases locρ with ⟨J, J_an, H_eq, a1, a2, a3, gval⟩
  -- This matches the removable lemma exactly at the center ρ:
  --   needs (ρ ≠ star ρ), (ρ ≠ oneMinus ρ), (ρ ≠ oneMinus (star ρ)),
  --   and the value with W_at_rho.
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := ρ) hfacρ J J_an H_eq a1 a2 a3 gval


/--
Second step: analyticity of `G` at `star ρ`.

We reuse the same removable lemma, now with center `ρ' := star ρ`.
The three separation hypotheses at `star ρ` are re-routed to the lemma’s
expected shape with a couple of `simp` rewrites.
-/
theorem analytic_at_conj_from_local
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfacρ' :
    Hyperlocal.Factorization.FactorisedByQuartet H (star ρ) k G)
  (locρ' :
    ∃ J' : ℂ → ℂ,
      AnalyticAt ℂ J' (star ρ) ∧
      (∀ s, H s = (s - star ρ)^k * J' s) ∧
      star ρ ≠ ρ ∧
      star ρ ≠ Hyperlocal.oneMinus ρ ∧
      star ρ ≠ Hyperlocal.oneMinus (star ρ) ∧
      G (star ρ) = J' (star ρ) / Hyperlocal.FactorizationAnalytic.W_at_rho (star ρ) k (star ρ)) :
  AnalyticAt ℂ G (star ρ) := by
  rcases locρ' with ⟨J', J'_an, H_eq', b1, b2, b3, gval'⟩
  -- Prepare the three separations in the exact shapes the removable lemma expects.
  -- ρ' := star ρ
  have h1' : (star ρ) ≠ star (star ρ) := by
    -- target: star ρ ≠ star (star ρ)  ~  b1: star ρ ≠ ρ
    simpa [star_star] using b1
  have h2' : (star ρ) ≠ Hyperlocal.oneMinus (star ρ) := by
    -- this exactly matches b3
    simpa using b3
  have h3' : (star ρ) ≠ Hyperlocal.oneMinus (star (star ρ)) := by
    -- target: star ρ ≠ 1 - star (star ρ)  ~  b2: star ρ ≠ 1 - ρ
    simpa [Hyperlocal.oneMinus, star_star] using b2
  -- Apply the same removable lemma at center ρ' = star ρ.
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := star ρ) hfacρ' J' J'_an H_eq' h1' h2' h3' gval'

/--
Third step: analyticity of `G` at `1 - ρ`.

We apply the same removable lemma with center `ρ' := oneMinus ρ`.
The three separations are rewritten into the lemma’s expected shapes.
-/
theorem analytic_at_oneMinus_from_local
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac1mρ :
    Hyperlocal.Factorization.FactorisedByQuartet H (oneMinus ρ) k G)
  (loc1mρ :
    ∃ J₁ : ℂ → ℂ,
      AnalyticAt ℂ J₁ (oneMinus ρ) ∧
      (∀ s, H s = (s - oneMinus ρ)^k * J₁ s) ∧
      oneMinus ρ ≠ ρ ∧
      oneMinus ρ ≠ star ρ ∧
      oneMinus ρ ≠ Hyperlocal.oneMinus (star ρ) ∧
      G (oneMinus ρ) =
        J₁ (oneMinus ρ) /
          Hyperlocal.FactorizationAnalytic.W_at_rho (oneMinus ρ) k (oneMinus ρ)) :
  AnalyticAt ℂ G (oneMinus ρ) := by
  rcases loc1mρ with ⟨J₁, J₁_an, H_eq₁, c1, c2, c3, gval₁⟩
  -- Center `ρ' := oneMinus ρ`. Prepare the three separations in lemma form.
  have h1' : (oneMinus ρ) ≠ star (oneMinus ρ) := by
    -- `star (oneMinus ρ) = oneMinus (star ρ)`
    simpa [Hyperlocal.oneMinus, star_sub, star_one] using c3
  have h2' : (oneMinus ρ) ≠ Hyperlocal.oneMinus (oneMinus ρ) := by
    -- `oneMinus (oneMinus ρ) = ρ`
    simpa [Hyperlocal.oneMinus] using c1
  have h3' : (oneMinus ρ) ≠ Hyperlocal.oneMinus (star (oneMinus ρ)) := by
    -- `oneMinus (star (oneMinus ρ)) = star ρ`
    simpa [Hyperlocal.oneMinus, star_sub, star_one] using c2
  -- Apply removable lemma at center `ρ' = oneMinus ρ`.
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := oneMinus ρ) hfac1mρ J₁ J₁_an H_eq₁ h1' h2' h3' gval₁

/--
Fourth step: analyticity of `G` at `1 - star ρ`.

We apply the removable lemma with center `ρ' := oneMinus (star ρ)`.
The three separations are rewritten into the lemma’s required forms.
-/
theorem analytic_at_oneMinus_conj_from_local
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac1mρ' :
    Hyperlocal.Factorization.FactorisedByQuartet H (oneMinus (star ρ)) k G)
  (loc1mρ' :
    ∃ J₃ : ℂ → ℂ,
      AnalyticAt ℂ J₃ (oneMinus (star ρ)) ∧
      (∀ s, H s = (s - oneMinus (star ρ))^k * J₃ s) ∧
      oneMinus (star ρ) ≠ ρ ∧
      oneMinus (star ρ) ≠ star ρ ∧
      oneMinus (star ρ) ≠ oneMinus ρ ∧
      G (oneMinus (star ρ)) =
        J₃ (oneMinus (star ρ)) /
          Hyperlocal.FactorizationAnalytic.W_at_rho (oneMinus (star ρ)) k (oneMinus (star ρ))) :
  AnalyticAt ℂ G (oneMinus (star ρ)) := by
  rcases loc1mρ' with ⟨J₃, J₃_an, H_eq₃, d1, d2, d3, gval₃⟩
  -- Center ρ' = oneMinus (star ρ). Rewrite the three separations into the lemma’s shapes.
  have h1' : oneMinus (star ρ) ≠ star (oneMinus (star ρ)) := by
    -- star (oneMinus (star ρ)) = oneMinus ρ
    simpa [Hyperlocal.oneMinus, star_sub, star_one] using d3
  have h2' : oneMinus (star ρ) ≠ Hyperlocal.oneMinus (oneMinus (star ρ)) := by
    -- oneMinus (oneMinus (star ρ)) = star ρ
    simpa [Hyperlocal.oneMinus] using d2
  have h3' : oneMinus (star ρ) ≠ Hyperlocal.oneMinus (star (oneMinus (star ρ))) := by
    -- star (oneMinus (star ρ)) = oneMinus ρ, then oneMinus (oneMinus ρ) = ρ
    simpa [Hyperlocal.oneMinus, star_sub, star_one] using d1
  -- Apply the removable lemma at ρ' = oneMinus (star ρ).
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := oneMinus (star ρ))
      hfac1mρ' J₃ J₃_an H_eq₃ h1' h2' h3' gval₃

/-! ## Entirety of `G` -/
theorem entire_G_of_factorisation
  {H G : ℂ → ℂ} {rho : ℂ} {k : ℕ}
  -- global factorization at each quartet anchor
  (hfac_rho     : Factorization.FactorisedByQuartet H rho k G)
  (hfac_conj    : Factorization.FactorisedByQuartet H (star rho) k G)
  (hfac_1mrho   : Factorization.FactorisedByQuartet H (oneMinus rho) k G)
  (hfac_1mconj  : Factorization.FactorisedByQuartet H (oneMinus (star rho)) k G)
  -- H is entire
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
  -- local expansions and removable values at each quartet point
  (loc_rho :
    ∃ J, AnalyticAt ℂ J rho ∧ (∀ s, H s = (s - rho)^k * J s) ∧
          rho ≠ star rho ∧ rho ≠ oneMinus rho ∧ rho ≠ oneMinus (star rho) ∧
          G rho = J rho / FactorizationAnalytic.W_at_rho rho k rho)
  (loc_conj :
    ∃ J', AnalyticAt ℂ J' (star rho) ∧ (∀ s, H s = (s - star rho)^k * J' s) ∧
           star rho ≠ rho ∧ star rho ≠ oneMinus rho ∧ star rho ≠ oneMinus (star rho) ∧
           G (star rho) = J' (star rho) / FactorizationAnalytic.W_at_rho (star rho) k (star rho))
  (loc_1mrho :
    ∃ J₂, AnalyticAt ℂ J₂ (oneMinus rho) ∧ (∀ s, H s = (s - oneMinus rho)^k * J₂ s) ∧
           oneMinus rho ≠ rho ∧ oneMinus rho ≠ star rho ∧ oneMinus rho ≠ oneMinus (star rho) ∧
           G (oneMinus rho) = J₂ (oneMinus rho) / FactorizationAnalytic.W_at_rho (oneMinus rho) k (oneMinus rho))
  (loc_1mconj :
    ∃ J₃, AnalyticAt ℂ J₃ (oneMinus (star rho)) ∧
           (∀ s, H s = (s - oneMinus (star rho))^k * J₃ s) ∧
           oneMinus (star rho) ≠ rho ∧ oneMinus (star rho) ≠ star rho ∧
           oneMinus (star rho) ≠ oneMinus rho ∧
           G (oneMinus (star rho)) = J₃ (oneMinus (star rho)) /
             FactorizationAnalytic.W_at_rho (oneMinus (star rho)) k (oneMinus (star rho))) :
  ∀ z : ℂ, AnalyticAt ℂ G z := by
  intro z
  classical
  -- split on the quartet
  by_cases hz0 : z = rho
  · subst hz0
    -- use your wrapper at rho (no named args; Lean infers {ρ := rho} and {k})
    exact analytic_at_rho_from_local hfac_rho loc_rho
  · by_cases hz1 : z = star rho
    · subst hz1
      exact analytic_at_conj_from_local hfac_conj loc_conj
    · by_cases hz2 : z = oneMinus rho
      · subst hz2
        exact analytic_at_oneMinus_from_local hfac_1mrho loc_1mrho
      · by_cases hz3 : z = oneMinus (star rho)
        · subst hz3
          exact analytic_at_oneMinus_conj_from_local hfac_1mconj loc_1mconj
        ·
          -- off-quartet: your existing lemma
          exact Hyperlocal.FactorizationAnalytic.G_analytic_off_quartet
            hfac_rho H_an
            (by simpa using hz0) (by simpa using hz1)
            (by simpa using hz2) (by simpa using hz3)

end FactorizationGofSEntire
end Hyperlocal
