/-
  FactorizationGofSEntire.lean

  Minimal step: prove G is analytic at the four quartet anchors using the removable lemma,
  then conclude ∀ z, AnalyticAt ℂ G z by splitting on the quartet and using
  `G_analytic_off_quartet` off the quartet.
-/

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
  (hfacρ : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
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
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := ρ) hfacρ J J_an H_eq a1 a2 a3 gval

/--
Second step: analyticity of `G` at `star ρ`.
-/
theorem analytic_at_conj_from_local
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfacρ' : Hyperlocal.Factorization.FactorisedByQuartet H (star ρ) k G)
  (locρ' :
    ∃ J' : ℂ → ℂ,
      AnalyticAt ℂ J' (star ρ) ∧
      (∀ s, H s = (s - star ρ)^k * J' s) ∧
      star ρ ≠ ρ ∧
      star ρ ≠ Hyperlocal.oneMinus ρ ∧
      star ρ ≠ Hyperlocal.oneMinus (star ρ) ∧
      G (star ρ) =
        J' (star ρ) /
          Hyperlocal.FactorizationAnalytic.W_at_rho (star ρ) k (star ρ)) :
  AnalyticAt ℂ G (star ρ) := by
  rcases locρ' with ⟨J', J'_an, H_eq', b1, b2, b3, gval'⟩
  have h1' : (star ρ) ≠ star (star ρ) := by
    simpa [star_star] using b1
  have h2' : (star ρ) ≠ Hyperlocal.oneMinus (star ρ) := by
    simpa using b3
  have h3' : (star ρ) ≠ Hyperlocal.oneMinus (star (star ρ)) := by
    simpa [Hyperlocal.oneMinus, star_star] using b2
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := star ρ) hfacρ' J' J'_an H_eq' h1' h2' h3' gval'

/--
Third step: analyticity of `G` at `1 - ρ`.
-/
theorem analytic_at_oneMinus_from_local
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac1mρ : Hyperlocal.Factorization.FactorisedByQuartet H (oneMinus ρ) k G)
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
  have h1' : (oneMinus ρ) ≠ star (oneMinus ρ) := by
    -- star (1 - ρ) = 1 - star ρ
    simpa [Hyperlocal.oneMinus, star_sub, star_one] using c3
  have h2' : (oneMinus ρ) ≠ Hyperlocal.oneMinus (oneMinus ρ) := by
    -- 1 - (1 - ρ) = ρ
    simpa [Hyperlocal.oneMinus] using c1
  have h3' : (oneMinus ρ) ≠ Hyperlocal.oneMinus (star (oneMinus ρ)) := by
    -- star (1 - ρ) = 1 - star ρ, and 1 - (1 - star ρ) = star ρ
    simpa [Hyperlocal.oneMinus, star_sub, star_one] using c2
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := oneMinus ρ) hfac1mρ J₁ J₁_an H_eq₁ h1' h2' h3' gval₁

/--
Fourth step: analyticity of `G` at `1 - star ρ`.
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
          Hyperlocal.FactorizationAnalytic.W_at_rho (oneMinus (star ρ)) k
            (oneMinus (star ρ))) :
  AnalyticAt ℂ G (oneMinus (star ρ)) := by
  rcases loc1mρ' with ⟨J₃, J₃_an, H_eq₃, d1, d2, d3, gval₃⟩
  have h1' : oneMinus (star ρ) ≠ star (oneMinus (star ρ)) := by
    -- star (1 - star ρ) = 1 - ρ
    simpa [Hyperlocal.oneMinus, star_sub, star_one, star_star] using d3
  have h2' : oneMinus (star ρ) ≠ Hyperlocal.oneMinus (oneMinus (star ρ)) := by
    -- 1 - (1 - star ρ) = star ρ
    simpa [Hyperlocal.oneMinus] using d2
  have h3' : oneMinus (star ρ) ≠ Hyperlocal.oneMinus (star (oneMinus (star ρ))) := by
    -- star (1 - star ρ) = 1 - ρ, then 1 - (1 - ρ) = ρ
    simpa [Hyperlocal.oneMinus, star_sub, star_one, star_star] using d1
  simpa using
    Hyperlocal.FactorizationAnalytic.G_analytic_at_rho_of_value
      (ρ := oneMinus (star ρ))
      hfac1mρ' J₃ J₃_an H_eq₃ h1' h2' h3' gval₃

/-! ## Entirety of `G` -/

/--
Glue the four removable-analyticity facts with the off-quartet lemma to get
`∀ z, AnalyticAt ℂ G z`.
-/
theorem entire_G_of_factorisation
  {H G : ℂ → ℂ} {rho : ℂ} {k : ℕ}
  (hfac_rho     : Factorization.FactorisedByQuartet H rho k G)
  (hfac_conj    : Factorization.FactorisedByQuartet H (star rho) k G)
  (hfac_1mrho   : Factorization.FactorisedByQuartet H (oneMinus rho) k G)
  (hfac_1mconj  : Factorization.FactorisedByQuartet H (oneMinus (star rho)) k G)
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
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
           G (oneMinus rho) =
             J₂ (oneMinus rho) / FactorizationAnalytic.W_at_rho (oneMinus rho) k (oneMinus rho))
  (loc_1mconj :
    ∃ J₃, AnalyticAt ℂ J₃ (oneMinus (star rho)) ∧
           (∀ s, H s = (s - oneMinus (star rho))^k * J₃ s) ∧
           oneMinus (star rho) ≠ rho ∧ oneMinus (star rho) ≠ star rho ∧
           oneMinus (star rho) ≠ oneMinus rho ∧
           G (oneMinus (star rho)) =
             J₃ (oneMinus (star rho)) /
               FactorizationAnalytic.W_at_rho (oneMinus (star rho)) k (oneMinus (star rho))) :
  ∀ z : ℂ, AnalyticAt ℂ G z := by
  intro z
  classical
  by_cases hz0 : z = rho
  · subst hz0
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
          exact Hyperlocal.FactorizationAnalytic.G_analytic_off_quartet
            hfac_rho H_an
            (by simpa using hz0) (by simpa using hz1)
            (by simpa using hz2) (by simpa using hz3)

end FactorizationGofSEntire
end Hyperlocal
