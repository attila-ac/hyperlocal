import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace Hyperlocal

open Complex

/-- The affine involution `z ↦ 1 - z`. -/
def oneMinus (z : ℂ) : ℂ := 1 - z

/-- RC step: from `H ρ = 0` and `RC`, get `H (star ρ) = 0`. -/
lemma zero_star_of_zero
    (H  : ℂ → ℂ)
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (star ρ) = 0 := by
  simpa [h] using RC ρ

/-- FE step: from `H ρ = 0` and `FE`, get `H (oneMinus ρ) = 0`. -/
lemma zero_oneMinus_of_zero
    (H  : ℂ → ℂ)
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    {ρ : ℂ} (h : H ρ = 0) :
    H (oneMinus ρ) = 0 := by
  have : 0 = H (oneMinus ρ) := by simpa [h] using FE ρ
  simpa using this.symm

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
  · -- Goal 1: H ρ = 0
    exact h
  · constructor
    · -- Goal 2: H (star ρ) = 0
      exact zero_star_of_zero H RC h
    · constructor
      · -- Goal 3: H (oneMinus ρ) = 0
        exact zero_oneMinus_of_zero H FE h
      · -- Goal 4: H (oneMinus (star ρ)) = 0
        exact zero_oneMinus_star_of_zero H FE RC h

end Hyperlocal
