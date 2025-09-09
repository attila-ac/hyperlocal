import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace Hyperlocal

/-- The affine involution `z ↦ 1 - z`. -/
def oneMinus (z : ℂ) : ℂ := 1 - z

@[simp]
lemma oneMinus_oneMinus (z : ℂ) : oneMinus (oneMinus z) = z := by
  simp [oneMinus]

@[simp]
lemma oneMinus_star (z : ℂ) : oneMinus (star z) = star (oneMinus z) := by
  simp [oneMinus, star_one, star_sub]

/-- RC step: from `H ρ = 0` and `RC`, get `H (star ρ) = 0`. -/
lemma zero_star_of_zero
    (H  : ℂ → ℂ)
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (star ρ) = 0 := by
  rw [RC ρ, h, star_zero]

/-- FE step: from `H ρ = 0` and `FE`, get `H (oneMinus ρ) = 0`. -/
lemma zero_oneMinus_of_zero
    (H  : ℂ → ℂ)
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (oneMinus ρ) = 0 := by
  rw [← FE ρ]
  exact h

/-- Compose FE after RC: from `H ρ = 0`, get `H (oneMinus (star ρ)) = 0`. -/
lemma zero_oneMinus_star_of_zero
    (H  : ℂ → ℂ)
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (oneMinus (star ρ)) = 0 := by
  have hstar : H (star ρ) = 0 := zero_star_of_zero H RC h
  exact zero_oneMinus_of_zero H FE (ρ := star ρ) hstar

/-- Off-zero quartet: zeros at `ρ`, `star ρ`, `oneMinus ρ`, `oneMinus (star ρ)`. -/
lemma zero_quartet
    (H  : ℂ → ℂ)
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    {ρ : ℂ} (h : H ρ = 0) :
    H ρ = 0 ∧ H (star ρ) = 0 ∧ H (oneMinus ρ) = 0 ∧ H (oneMinus (star ρ)) = 0 := by
  constructor
  · exact h
  · constructor
    · exact zero_star_of_zero H RC h
    · constructor
      · exact zero_oneMinus_of_zero H FE h
      · exact zero_oneMinus_star_of_zero H FE RC h

end Hyperlocal
