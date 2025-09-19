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
  have h_prod :
      deriv (𝕜 := ℂ) (fun z => R z * G z) s
        = deriv (𝕜 := ℂ) R s * G s
          + R s * deriv (𝕜 := ℂ) G s := by
    simpa using deriv_mul (𝕜 := ℂ) (hR.differentiableAt) (hG.differentiableAt)
  have h_aff : deriv (𝕜 := ℂ) (fun z => R z * G z) s = α * s + β := by
    simpa using congrArg (fun f => f s) hH_affine
  have h_eq : α * s + β
      = deriv (𝕜 := ℂ) R s * G s + R s * deriv (𝕜 := ℂ) G s := by
    simpa [h_aff] using h_prod
  simpa [add_comm] using h_eq.symm

/-- Pointwise product rule for the square map: `d/ds (s*s) = s + s` at a given `s`. -/
lemma deriv_sq_at (s : ℂ) :
    deriv (𝕜 := ℂ) (fun z : ℂ => z * z) s = s + s := by
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => z) s :=
    differentiable_id.differentiableAt
  have h₂ : DifferentiableAt ℂ (fun z : ℂ => z) s :=
    differentiable_id.differentiableAt
  have h := deriv_mul (𝕜 := ℂ) h₁ h₂
  simp [deriv_id'] at h
  simpa using h

/-- Pointwise product rule for the linear term: `d/ds (s * β) = β` at `s`. -/
lemma deriv_linear_right_at (β s : ℂ) :
    deriv (𝕜 := ℂ) (fun z : ℂ => z * β) s = β := by
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => z) s :=
    differentiable_id.differentiableAt
  have h₂ : DifferentiableAt ℂ (fun _ : ℂ => β) s :=
    (differentiable_const β).differentiableAt
  have h := deriv_mul (𝕜 := ℂ) h₁ h₂
  simp [deriv_id', deriv_const] at h
  simpa using h

/-- Function-level wrappers. -/
lemma deriv_linear_right (β : ℂ) :
    deriv (𝕜 := ℂ) (fun s : ℂ => s * β) = (fun _ => β) := by
  funext s
  simpa using deriv_linear_right_at β s

lemma deriv_sq :
    deriv (𝕜 := ℂ) (fun s : ℂ => s * s) = (fun s => s + s) := by
  funext s
  simpa using deriv_sq_at s

/-- Clean lemma: derivative of `(α/2) * s^2 + β * s` is `α*s + β` (pointwise at `s`). -/
lemma deriv_quad_affine_at (α β s : ℂ) :
    deriv (𝕜 := ℂ) (fun z : ℂ => (α/2) * z^2 + β * z) s = α * s + β := by
  -- HasDerivAt for the square map: `d/dz (z*z) = s + s` at `s`.
  have hsq : HasDerivAt (fun z : ℂ => z * z) (s + s) s := by
    -- product rule on `id * id`, then simplify the function and the derivative value
    simpa [id, one_mul, mul_one] using (hasDerivAt_id s).mul (hasDerivAt_id s)

  -- Derivative of the quadratic piece via constant-left multiplication.
  have h1 : deriv (𝕜 := ℂ) (fun z : ℂ => (α/2) * (z * z)) s = (α/2) * (s + s) := by
    simpa using (hsq.const_mul (α/2)).deriv

  -- Derivative of the linear piece `β * z` is `β`.
  have h2 : deriv (𝕜 := ℂ) (fun z : ℂ => β * z) s = β := by
    simpa using ((hasDerivAt_id s).const_mul β).deriv

  -- Sum rule at `s` (we supply the DifferentiableAt facts expected by `deriv_add`).
  have hsum :
      deriv (𝕜 := ℂ) (fun z : ℂ => (α/2) * (z*z) + β * z) s
        = (α/2) * (s + s) + β := by
    have hquad_d : DifferentiableAt ℂ (fun z : ℂ => (α/2) * (z*z)) s :=
      (hsq.const_mul (α/2)).differentiableAt
    have hlin_d  : DifferentiableAt ℂ (fun z : ℂ => β * z) s :=
      ((hasDerivAt_id s).const_mul β).differentiableAt
    simpa [h1, h2] using deriv_add (𝕜 := ℂ) hquad_d hlin_d

  -- Rewrite `z^2` as `z*z` in the function, then finish the arithmetic `(α/2)*(s+s) = α*s`.
  have hsum_pow :
      deriv (𝕜 := ℂ) (fun z : ℂ => (α/2) * z^2 + β * z) s
        = (α/2) * (s + s) + β := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsum

  have harr : (α/2) * (s + s) = α * s := by
    have : (2 : ℂ) * s = s + s := by simpa [two_mul]
    calc
      (α/2) * (s + s) = (α/2) * ((2 : ℂ) * s) := by simpa [this]
      _ = ((α/2) * (2 : ℂ)) * s := by ring_nf
      _ = α * s := by simp [div_eq_mul_inv]

  simpa [harr] using hsum_pow


lemma deriv_RG_minus_quad_is_zero_at
    {R G : ℂ → ℂ} {α β : ℂ}
    (hR : Differentiable ℂ R) (hG : Differentiable ℂ G)
    (hH_affine : deriv (fun s => R s * G s) = fun s => α*s + β)
    (s : ℂ) :
    deriv (fun z => R z * G z - ((α/2) * z^2 + β * z)) s = 0 := by
  have hRGd : DifferentiableAt ℂ (fun z => R z * G z) s :=
    (hR.differentiableAt).mul (hG.differentiableAt)
  -- differentiability of (α/2) * z^2 + β * z at s
  have hQ : Differentiable ℂ (fun z : ℂ => (α/2) * z^2 + β * z) :=
    ((differentiable_const (α/2)).mul (differentiable_pow 2)).add
      ((differentiable_const β).mul differentiable_id)

  have hQd : DifferentiableAt ℂ (fun z : ℂ => (α/2) * z^2 + β * z) s :=
    hQ.differentiableAt

  -- expand derivative of difference
  have h_sub := deriv_sub (𝕜 := ℂ) hRGd hQd
  calc
    deriv (fun z => R z * G z - ((α/2) * z^2 + β*z)) s
        = deriv (fun z => R z * G z) s - deriv (fun z => (α/2) * z^2 + β*z) s :=
      h_sub
    _ = (α*s + β) - (α*s + β) := by
      rw [congrFun hH_affine s, deriv_quad_affine_at α β s]
    _ = 0 := by ring

  -- derivative of the affine RHS at s
  have h_quad : deriv (fun z : ℂ => (α/2) * z^2 + β * z) s = α * s + β := by
    -- you already have a lemma `deriv_quad_affine_at`; if not, `simp` also works via `deriv_pow`
    simpa using deriv_quad_affine_at α β s

  -- use the hypothesis at the point s
  have h_aff_pt : deriv (fun z => R z * G z) s = α * s + β := by
    simpa using congrArg (fun f => f s) hH_affine

  -- apply `deriv_sub`, then substitute both sides and finish by `simp`
  have : deriv (fun z => R z * G z - ((α/2) * z^2 + β * z)) s
        = (α * s + β) - (α * s + β) := by
    have h_sub :
        deriv (fun z => R z * G z - ((α/2) * z^2 + β * z)) s
        = deriv (fun z => R z * G z) s
          - deriv (fun z : ℂ => (α/2) * z^2 + β * z) s := by
      simpa using deriv_sub (𝕜 := ℂ) hRGd hQd
    simpa [h_aff_pt, h_quad] using h_sub

  simpa using this





end NoPolyG_DE
end Hyperlocal
