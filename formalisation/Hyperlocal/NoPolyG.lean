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

end NoPolyG_DE
end Hyperlocal
