import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace NoPolyG_DE

/--
If `H(s) = R(s)*G(s)` has derivative `α*s + β`, then
`R(s)*G'(s) + R'(s)*G(s) = α*s + β` for all `s : ℂ`.
-/
lemma ode_product_form
    {R G : ℂ → ℂ} {α β : ℂ}
    (hR : Differentiable ℂ R)
    (hG : Differentiable ℂ G)
    (hH_affine : deriv (𝕜 := ℂ) (fun s => R s * G s) = (fun s => α * s + β)) :
    ∀ s : ℂ,
      R s * deriv (𝕜 := ℂ) G s
      + deriv (𝕜 := ℂ) R s * G s
      = α * s + β := by
  intro s
  -- product rule at `s`
  have h_prod :
      deriv (𝕜 := ℂ) (fun z => R z * G z) s
        = deriv (𝕜 := ℂ) R s * G s
          + R s * deriv (𝕜 := ℂ) G s := by
    simpa using deriv_mul (𝕜 := ℂ) (hR.differentiableAt) (hG.differentiableAt)
  -- hypothesis “H' = α s + β”, pointwise
  have h_aff : deriv (𝕜 := ℂ) (fun z => R z * G z) s = α * s + β := by
    simpa using congrArg (fun f => f s) hH_affine
  -- rewrite, then flip orientation and reorder to match the goal
  have h_eq : α * s + β
      = deriv (𝕜 := ℂ) R s * G s + R s * deriv (𝕜 := ℂ) G s := by
    simpa [h_aff] using h_prod
  simpa [add_comm] using h_eq.symm

/-- Pointwise product rule for the square map: `d/ds (s*s) = s + s` at a given `s`. -/
lemma deriv_sq_at (s : ℂ) :
    deriv (𝕜 := ℂ) (fun z : ℂ => z * z) s = s + s := by
  -- Make the `id` differentiability explicit at this `s`.
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => z) s :=
    differentiable_id.differentiableAt
  have h₂ : DifferentiableAt ℂ (fun z : ℂ => z) s :=
    differentiable_id.differentiableAt
  -- Product rule at `s`.
  have h := deriv_mul (𝕜 := ℂ) h₁ h₂
  -- `deriv id s = 1`, so `(1)*s + s*(1) = s + s`.
  simpa [deriv_id'] using h

/-- Pointwise product rule for the linear term: `d/ds (s * β) = β` at `s`. -/
lemma deriv_linear_right_at (β s : ℂ) :
    deriv (𝕜 := ℂ) (fun z : ℂ => z * β) s = β := by
  -- make the `DifferentiableAt … s` facts explicit
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => z) s :=
    differentiable_id.differentiableAt
  have h₂ : DifferentiableAt ℂ (fun _ : ℂ => β) s :=
    (differentiable_const β).differentiableAt
  -- product rule at `s`
  have h := deriv_mul (𝕜 := ℂ) h₁ h₂
  -- `deriv id s = 1`, `deriv const s = 0`
  simpa [deriv_id', deriv_const] using h

-- keep your existing pointwise lemma:
-- lemma deriv_sq_at (s : ℂ) : deriv (𝕜 := ℂ) (fun z => z * z) s = s + s := by ...

-- add wrappers without introducing new names that collide:
lemma deriv_linear_right (β : ℂ) :
    deriv (𝕜 := ℂ) (fun s : ℂ => s * β) = (fun _ => β) := by
  funext s
  simpa using deriv_linear_right_at β s

lemma deriv_sq :
    deriv (𝕜 := ℂ) (fun s : ℂ => s * s) = (fun s => s + s) := by
  funext s
  simpa using deriv_sq_at s

/-- Pointwise: `d/ds ((s*s)*(α/2) + s*β) = α*s + β` at `s`. -/
lemma deriv_quad_affine_at (α β s : ℂ) :
    deriv (𝕜 := ℂ) (fun z : ℂ => (z*z)*(α/2) + z*β) s = α*s + β := by
  -- quadratic part: treat as (z*z) * const
  have d_quad :
      deriv (𝕜 := ℂ) (fun z : ℂ => (z*z)*(α/2)) s
        = (s + s) * (α/2) := by
    -- product rule for (z*z) * (α/2)
    have h₁ : DifferentiableAt ℂ (fun z : ℂ => z*z) s :=
      (differentiable_id.differentiableAt).mul (differentiable_id.differentiableAt)
    have h₂ : DifferentiableAt ℂ (fun _ : ℂ => (α/2)) s :=
      (differentiable_const (α/2)).differentiableAt
    have h := deriv_mul (𝕜 := ℂ) h₁ h₂
    -- `deriv (z*z) s = s+s` and `deriv const s = 0`
    simpa [deriv_sq_at s, deriv_const] using h

  -- linear part: your lemma
  have d_lin : deriv (𝕜 := ℂ) (fun z : ℂ => z*β) s = β :=
    deriv_linear_right_at β s

  -- sum rule
  have hsum :
      deriv (𝕜 := ℂ) (fun z : ℂ => (z*z)*(α/2) + z*β) s
        = (s + s) * (α/2) + β := by
    -- `deriv_add` rewrites the derivative of a sum
    simp [deriv_add, d_quad, d_lin]

  -- arithmetic: (s+s)*(α/2) = α*s
  have harr : (s + s) * (α/2) = α * s := by
    -- commute once, distribute, then combine with `ring`
    calc
      (s + s) * (α / 2) = (α / 2) * (s + s) := by ac_rfl
      _ = (α / 2) * s + (α / 2) * s := by simpa [mul_add]
      _ = ((α / 2) + (α / 2)) * s := by ring
      _ = α * s := by
        have : (α / 2) + (α / 2) = α := by ring
        simpa [this]

  -- put it together
  simpa [hsum, harr]


end NoPolyG_DE
end Hyperlocal
