/-
  Minimal RC+FE quartet: from H ρ = 0, RC : H (⋆s) = ⋆(H s),
  and FE : H s = H (1 - s), we get zeros at ρ, ⋆ρ, 1 - ρ, 1 - ⋆ρ.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace Hyperlocal

/-- From `H ρ = 0` and `RC : ∀ s, H (⋆s) = ⋆(H s)` we get `H (⋆ρ) = 0`. -/
lemma zero_star_of_zero
    (H  : ℂ → ℂ)
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (star ρ) = 0 := by
  simpa [h] using RC ρ

/-- The affine involution `z ↦ 1 - z`. -/
def oneMinus (z : ℂ) : ℂ := 1 - z

/-- From `H ρ = 0` and `FE : ∀ s, H s = H (1 - s)` we get `H (1 - ρ) = 0`. -/
lemma zero_oneMinus_of_zero
    (H  : ℂ → ℂ)
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (oneMinus ρ) = 0 := by
  have : 0 = H (oneMinus ρ) := by simpa [h] using FE ρ
  simpa [eq_comm] using this

/-- Off-zero quartet: from one zero and the symmetries RC and FE,
    all four points `ρ, ⋆ρ, 1 - ρ, 1 - ⋆ρ` are zeros of `H`. -/
lemma zero_quartet_of_zero
    (H  : ℂ → ℂ)
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    {ρ : ℂ} (h : H ρ = 0) :
    (H ρ = 0) ∧
    (H (star ρ) = 0) ∧
    (H (oneMinus ρ) = 0) ∧
    (H (oneMinus (star ρ)) = 0) := by
  have h_star : H (star ρ) = 0 := zero_star_of_zero H RC h
  have h_one  : H (oneMinus ρ) = 0 := zero_oneMinus_of_zero H FE h
  have h_one_star : H (oneMinus (star ρ)) = 0 :=
    zero_oneMinus_of_zero H FE h_star
  exact ⟨h, h_star, h_one, h_one_star⟩

end Hyperlocal
