import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic  -- For eval_pow, eval_sub, eval_X, eval_C

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization
import Hyperlocal.FactorizationGofSAnalytic  -- eval_Rρk_explicit, G_analytic_off_quartet

noncomputable section
open Complex Polynomial
open scoped BigOperators Topology

namespace Hyperlocal
namespace FactorizationGofSEntire

open Hyperlocal.FactorizationAnalytic  -- eval_Rρk_explicit, G_analytic_off_quartet

/-- The product of the “other three” factors at `ρ`, i.e. without `(s-ρ)^k`. -/
def W_at_rho (ρ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  (s - star ρ) ^ k * ((s - Hyperlocal.oneMinus ρ) ^ k * (s - Hyperlocal.oneMinus (star ρ)) ^ k)

/-- Factorization of the denominator near `ρ`: `(Rρk ρ k).eval s = (s-ρ)^k * W_at_rho ρ k s`. -/
lemma R_eval_eq_at_rho (ρ : ℂ) (k : ℕ) (s : ℂ) :
    (Hyperlocal.Factorization.Rρk ρ k).eval s
  = (s - ρ) ^ k * W_at_rho ρ k s := by
  classical
  simp [Hyperlocal.Factorization.Rρk,
        Hyperlocal.MinimalModel.quartetPolyPow,
        Hyperlocal.MinimalModel.lin, Hyperlocal.MinimalModel.linPow,
        eval_pow, eval_sub, eval_X, eval_C,
        W_at_rho, mul_comm, mul_left_comm, mul_assoc]

/-- `W_at_rho` is analytic at `ρ`. -/
lemma W_at_rho_analytic (ρ : ℂ) (k : ℕ) :
  AnalyticAt ℂ (fun s => W_at_rho ρ k s) ρ := by
  have a1 : AnalyticAt ℂ (fun s => (s - star ρ) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a2 : AnalyticAt ℂ (fun s => (s - Hyperlocal.oneMinus ρ) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  have a3 : AnalyticAt ℂ (fun s => (s - Hyperlocal.oneMinus (star ρ)) ^ k) ρ :=
    (analyticAt_id.sub analyticAt_const).pow k
  simp [W_at_rho] using a1.mul (a2.mul a3)

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
  have : (ρ - star ρ) ^ k * ((ρ - Hyperlocal.oneMinus ρ) ^ k * (ρ - Hyperlocal.oneMinus (star ρ)) ^ k) ≠ 0 :=
    mul_ne_zero nz1 (mul_ne_zero nz2 nz3)
  simp [W_at_rho] using this

/-- Removable singularity at `z = ρ`. -/
theorem G_analytic_at_rho
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
  (locρ : ∃ J, AnalyticAt ℂ J ρ ∧
      (∀ s, H s = (s - ρ)^k * J s) ∧
      ρ ≠ star ρ ∧ ρ ≠ oneMinus ρ ∧ ρ ≠ oneMinus (star ρ) ∧
      G ρ = J ρ / W_at_rho ρ k ρ) :
  AnalyticAt ℂ G ρ := by
  classical
  rcases locρ with ⟨J, J_an, H_eq, a1, a2, a3, gval⟩
  have R_eq := R_eval_eq_at_rho ρ k
  have W_an := W_at_rho_analytic ρ k
  have W_ne0 := W_at_rho_ne_zero_at_rho a1 a2 a3
  let F : ℂ → ℂ := fun s => J s / W_at_rho ρ k s
  have F_an : AnalyticAt ℂ F ρ := J_an.div W_an W_ne0
  have hW₀ : ∀ᶠ s in nhds ρ, W_at_rho ρ k s ≠ 0 := W_an.continuousAt.eventually_ne W_ne0
  have h_eq : G =ᶠ[nhds ρ] F := by
    refine hW₀.mono ?_
    intro s hWs
    by_cases hsρ : s = ρ
    · subst hsρ
      simp [F, gval]
    · have hpow : (s - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hsρ)
      have hfac_s := hfac s
      have hH := H_eq s
      have hR := R_eq s
      have : (s - ρ)^k * J s = ((s - ρ)^k * W_at_rho ρ k s) * G s := by
        simp [hH, hR, mul_assoc] using hfac_s
      have J_eq : J s = W_at_rho ρ k s * G s := mul_left_cancel₀ hpow this
      have needed : G s * W_at_rho ρ k s = J s := by
        exact J_eq
      exact (eq_div_iff_mul_eq hWs).mpr needed
  exact F_an.congr h_eq.symm

/-- Analyticity of `G` at `star ρ`. -/
theorem G_analytic_at_star_rho
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
  (locstar : ∃ J, AnalyticAt ℂ J (star ρ) ∧
      (∀ s, H s = (s - star ρ)^k * J s) ∧
      star ρ ≠ ρ ∧ star ρ ≠ oneMinus ρ ∧ star ρ ≠ oneMinus (star ρ) ∧
      G (star ρ) = J (star ρ) / W_at_rho ρ k (star ρ)) :
  AnalyticAt ℂ G (star ρ) := by
  classical
  rcases locstar with ⟨J, J_an, H_eq, a1, a2, a3, gval⟩
  have R_eq s := R_eval_eq_at_rho ρ k s
  have W_an : AnalyticAt ℂ (fun s => W_at_rho ρ k s) (star ρ) := W_at_rho_analytic ρ k
  have W_ne0 := W_at_rho_ne_zero_at_rho a1 a2 a3
  let F : ℂ → ℂ := fun s => J s / W_at_rho ρ k s
  have F_an : AnalyticAt ℂ F (star ρ) := J_an.div W_an W_ne0
  have hW₀ : ∀ᶠ s in nhds (star ρ), W_at_rho ρ k s ≠ 0 := W_an.continuousAt.eventually_ne W_ne0
  have h_eq : G =ᶠ[nhds (star ρ)] F := by
    refine hW₀.mono ?_
    intro s hWs
    by_cases hs : s = star ρ
    · subst hs
      simp [F, gval]
    · have hpow : (s - star ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
      have hfac_s := hfac s
      have hH := H_eq s
      have hR := R_eq s
      have : (s - star ρ)^k * J s = ((s - ρ)^k * W_at_rho ρ k s) * G s := by
        sorry -- Adjust factorization for star ρ (e.g., Taylor shift)
      have J_eq : J s = W_at_rho ρ k s * G s := mul_left_cancel₀ hpow this
      have needed : G s * W_at_rho ρ k s = J s := by
        exact J_eq
      exact (eq_div_iff_mul_eq hWs).mpr needed
  exact F_an.congr h_eq.symm

/-- Analyticity of `G` at `oneMinus ρ`. -/
theorem G_analytic_at_oneMinus_rho
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
  (locone : ∃ J, AnalyticAt ℂ J (oneMinus ρ) ∧
      (∀ s, H s = (s - oneMinus ρ)^k * J s) ∧
      oneMinus ρ ≠ ρ ∧ oneMinus ρ ≠ star ρ ∧ oneMinus ρ ≠ oneMinus (star ρ) ∧
      G (oneMinus ρ) = J (oneMinus ρ) / W_at_rho ρ k (oneMinus ρ)) :
  AnalyticAt ℂ G (oneMinus ρ) := by
  classical
  rcases locone with ⟨J, J_an, H_eq, a1, a2, a3, gval⟩
  have R_eq s := R_eval_eq_at_rho ρ k s
  have W_an : AnalyticAt ℂ (fun s => W_at_rho ρ k s) (oneMinus ρ) := W_at_rho_analytic ρ k
  have W_ne0 := W_at_rho_ne_zero_at_rho a1 a2 a3
  let F : ℂ → ℂ := fun s => J s / W_at_rho ρ k s
  have F_an : AnalyticAt ℂ F (oneMinus ρ) := J_an.div W_an W_ne0
  have hW₀ : ∀ᶠ s in nhds (oneMinus ρ), W_at_rho ρ k s ≠ 0 := W_an.continuousAt.eventually_ne W_ne0
  have h_eq : G =ᶠ[nhds (oneMinus ρ)] F := by
    refine hW₀.mono ?_
    intro s hWs
    by_cases hs : s = oneMinus ρ
    · subst hs
      simp [F, gval]
    · have hpow : (s - oneMinus ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
      have hfac_s := hfac s
      have hH := H_eq s
      have hR := R_eq s
      have : (s - oneMinus ρ)^k * J s = ((s - ρ)^k * W_at_rho ρ k s) * G s := by
        sorry -- Adjust factorization for oneMinus ρ (e.g., Taylor shift)
      have J_eq : J s = W_at_rho ρ k s * G s := mul_left_cancel₀ hpow this
      have needed : G s * W_at_rho ρ k s = J s := by
        exact J_eq
      exact (eq_div_iff_mul_eq hWs).mpr needed
  exact F_an.congr h_eq.symm

/-- Analyticity of `G` at `oneMinus (star ρ)`. -/
theorem G_analytic_at_oneMinus_star_rho
  {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
  (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
  (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
  (locstar : ∃ J, AnalyticAt ℂ J (oneMinus (star ρ)) ∧
      (∀ s, H s = (s - oneMinus (star ρ))^k * J s) ∧
      oneMinus (star ρ) ≠ ρ ∧ oneMinus (star ρ) ≠ star ρ ∧ oneMinus (star ρ) ≠ oneMinus ρ ∧
      G (oneMinus (star ρ)) = J (oneMinus (star ρ)) / W_at_rho ρ k (oneMinus (star ρ)))) :
  AnalyticAt ℂ G (oneMinus (star ρ)) := by
  classical
  rcases locstar with ⟨J, J_an, H_eq, a1, a2, a3, gval⟩
  have R_eq s := R_eval_eq_at_rho ρ k s
  have W_an : AnalyticAt ℂ (fun s => W_at_rho ρ k s) (oneMinus (star ρ)) := W_at_rho_analytic ρ k
  have W_ne0 := W_at_rho_ne_zero_at_rho a1 a2 a3
  let F : ℂ → ℂ := fun s => J s / W_at_rho ρ k s
  have F_an : AnalyticAt ℂ F (oneMinus (star ρ)) := J_an.div W_an W_ne0
  have hW₀ : ∀ᶠ s in nhds (oneMinus (star ρ)), W_at_rho ρ k s ≠ 0 := W_an.continuousAt.eventually_ne W_ne0
  have h_eq : G =ᶠ[nhds (oneMinus (star ρ))] F := by
    refine hW₀.mono ?_
    intro s hWs
    by_cases hs : s = oneMinus (star ρ)
    · subst hs
      simp [F, gval]
    · have hpow : (s - oneMinus (star ρ)) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
      have hfac_s := hfac s
      have hH := H_eq s
      have hR := R_eq s
      have : (s - oneMinus (star ρ))^k * J s = ((s - ρ)^k * W_at_rho ρ k s) * G s := by
        sorry -- Adjust factorization for oneMinus (star ρ) (e.g., Taylor shift)
      have J_eq : J s = W_at_rho ρ k s * G s := mul_left_cancel₀ hpow this
      have needed : G s * W_at_rho ρ k s = J s := by
        exact J_eq
      exact (eq_div_iff_mul_eq hWs).mpr needed
  exact F_an.congr h_eq.symm

/-- G is entire if H is entire and H = R * G, with zeros of order at least k at the quartet. -/
lemma G_entire {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
    (H_an : ∀ z : ℂ, AnalyticAt ℂ H z)
    (h_zeros : ∀ z ∈ Hyperlocal.MinimalModel.quartetFinset ρ,
               ∃ m ≥ k, ∀ i < m, (deriv^[i] H) z = 0 ∧ (deriv^[m] H) z ≠ 0) :
    ∀ z, AnalyticAt ℂ G z := by
  classical
  let S := Hyperlocal.MinimalModel.quartetFinset ρ
  intro z
  by_cases hz : z ∈ S
  · simp only [S, Hyperlocal.MinimalModel.quartetFinset] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    cases hz with
    | inl h =>
      -- z = ρ
      subst h
      obtain ⟨m, hm, h_deriv⟩ := h_zeros ρ (Finset.mem_insert.mpr (Or.inl rfl))
      let J s := (s - ρ) ^ (m - k) * ((deriv^[m] H) ρ / (m)!)
      have J_an : AnalyticAt ℂ J ρ := by
        have : (deriv^[m] H) ρ / (m)! ≠ 0 := by
          simp [h_deriv m (le_refl m) |>.right, Nat.factorial_ne_zero]
        exact (analyticAt_const.mul this).mul ((analyticAt_id.sub analyticAt_const).pow (m - k))
      have H_eq : ∀ s, H s = (s - ρ)^k * J s := by
        intro s
        simp [J]
        sorry -- Prove H s = (s - ρ)^k * (s - ρ)^(m - k) * (deriv^[m] H) ρ / m! near ρ
      have h1 : ρ ≠ star ρ := by
        by_contra h; simp [h] at h_zeros; contradiction
      have h2 : ρ ≠ oneMinus ρ := by
        by_contra h; simp [h] at h_zeros; contradiction
      have h3 : ρ ≠ oneMinus (star ρ) := by
        by_contra h; simp [h] at h_zeros; contradiction
      have hGval : G ρ = J ρ / W_at_rho ρ k ρ := by
        sorry -- Prove G ρ = (deriv^[m] H) ρ / (m)! / W_at_rho ρ k ρ
      exact G_analytic_at_rho hfac H_an ⟨J, J_an, H_eq, h1, h2, h3, hGval⟩
    | inr h => cases h with
      | inl h =>
        -- z = star ρ
        subst h
        obtain ⟨m, hm, h_deriv⟩ := h_zeros (star ρ) (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl))))
        let J s := (s - star ρ) ^ (m - k) * ((deriv^[m] H) (star ρ) / (m)!)
        have J_an : AnalyticAt ℂ J (star ρ) := by
          have : (deriv^[m] H) (star ρ) / (m)! ≠ 0 := by
            simp [h_deriv m (le_refl m) |>.right, Nat.factorial_ne_zero]
          exact (analyticAt_const.mul this).mul ((analyticAt_id.sub analyticAt_const).pow (m - k))
        have H_eq : ∀ s, H s = (s - star ρ)^k * J s := by
          intro s
          simp [J]
          sorry -- Prove H s = (s - star ρ)^k * (s - star ρ)^(m - k) * (deriv^[m] H) (star ρ) / m! near star ρ
        have h1 : star ρ ≠ ρ := by
          by_contra h; simp [h] at h_zeros; contradiction
        have h2 : star ρ ≠ oneMinus ρ := by
          by_contra h; simp [h] at h_zeros; contradiction
        have h3 : star ρ ≠ oneMinus (star ρ) := by
          by_contra h; simp [h] at h_zeros; contradiction
        have hGval : G (star ρ) = J (star ρ) / W_at_rho ρ k (star ρ) := by
          sorry -- Prove G (star ρ) = (deriv^[m] H) (star ρ) / (m)! / W_at_rho ρ k (star ρ)
        exact G_analytic_at_star_rho hfac H_an ⟨J, J_an, H_eq, h1, h2, h3, hGval⟩
      | inr h => cases h with
        | inl h =>
          -- z = oneMinus ρ
          subst h
          obtain ⟨m, hm, h_deriv⟩ := h_zeros (oneMinus ρ) (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl))))))
          let J s := (s - oneMinus ρ) ^ (m - k) * ((deriv^[m] H) (oneMinus ρ) / (m)!)
          have J_an : AnalyticAt ℂ J (oneMinus ρ) := by
            have : (deriv^[m] H) (oneMinus ρ) / (m)! ≠ 0 := by
              simp [h_deriv m (le_refl m) |>.right, Nat.factorial_ne_zero]
            exact (analyticAt_const.mul this).mul ((analyticAt_id.sub analyticAt_const).pow (m - k))
          have H_eq : ∀ s, H s = (s - oneMinus ρ)^k * J s := by
            intro s
            simp [J]
            sorry -- Prove H s = (s - oneMinus ρ)^k * (s - oneMinus ρ)^(m - k) * (deriv^[m] H) (oneMinus ρ) / m! near oneMinus ρ
          have h1 : oneMinus ρ ≠ ρ := by
            by_contra h; simp [h] at h_zeros; contradiction
          have h2 : oneMinus ρ ≠ star ρ := by
            by_contra h; simp [h] at h_zeros; contradiction
          have h3 : oneMinus ρ ≠ oneMinus (star ρ) := by
            by_contra h; simp [h] at h_zeros; contradiction
          have hGval : G (oneMinus ρ) = J (oneMinus ρ) / W_at_rho ρ k (oneMinus ρ) := by
            sorry -- Prove G (oneMinus ρ) = (deriv^[m] H) (oneMinus ρ) / (m)! / W_at_rho ρ k (oneMinus ρ)
          exact G_analytic_at_oneMinus_rho hfac H_an ⟨J, J_an, H_eq, h1, h2, h3, hGval⟩
        | inr h =>
          -- z = oneMinus (star ρ)
          subst h
          obtain ⟨m, hm, h_deriv⟩ := h_zeros (oneMinus (star ρ)) (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))))))
          let J s := (s - oneMinus (star ρ)) ^ (m - k) * ((deriv^[m] H) (oneMinus (star ρ)) / (m)!)
          have J_an : AnalyticAt ℂ J (oneMinus (star ρ)) := by
            have : (deriv^[m] H) (oneMinus (star ρ)) / (m)! ≠ 0 := by
              simp [h_deriv m (le_refl m) |>.right, Nat.factorial_ne_zero]
            exact (analyticAt_const.mul this).mul ((analyticAt_id.sub analyticAt_const).pow (m - k))
          have H_eq : ∀ s, H s = (s - oneMinus (star ρ))^k * J s := by
            intro s
            simp [J]
            sorry -- Prove H s = (s - oneMinus (star ρ))^k * (s - oneMinus (star ρ))^(m - k) * (deriv^[m] H) (oneMinus (star ρ)) / m! near oneMinus (star ρ)
          have h1 : oneMinus (star ρ) ≠ ρ := by
            by_contra h; simp [h] at h_zeros; contradiction
          have h2 : oneMinus (star ρ) ≠ star ρ := by
            by_contra h; simp [h] at h_zeros; contradiction
          have h3 : oneMinus (star ρ) ≠ oneMinus ρ := by
            by_contra h; simp [h] at h_zeros; contradiction
          have hGval : G (oneMinus (star ρ)) = J (oneMinus (star ρ)) / W_at_rho ρ k (oneMinus (star ρ)) := by
            sorry -- Prove G (oneMinus (star ρ)) = (deriv^[m] H) (oneMinus (star ρ)) / (m)! / W_at_rho ρ k (oneMinus (star ρ))
          exact G_analytic_at_oneMinus_star_rho hfac H_an ⟨J, J_an, H_eq, h1, h2, h3, hGval⟩
  · -- Case: z is not in the quartet
    simp only [S, Hyperlocal.MinimalModel.quartetFinset] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    push_neg at hz
    exact G_analytic_off_quartet hfac H_an hz.left hz.right.left hz.right.right.left hz.right.right.right

end FactorizationGofSEntire
end Hyperlocal
