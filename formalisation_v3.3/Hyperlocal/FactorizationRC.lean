-- formalisation/Hyperlocal/FactorizationRC.lean
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization

/-
  Reality condition inheritance layer.
-/

noncomputable section
open Polynomial

namespace Hyperlocal
namespace FactorizationRC

-- These definitions are from your original working file.
/-- RC on scalar functions (mirrors `FunFE`). -/
def FunRC (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, F (star s) = star (F s)

/-- Value-level RC hypothesis for the quartet polynomial factor. -/
def RC_R (ρ : ℂ) (k : ℕ) : Prop :=
  ∀ s : ℂ,
    (Hyperlocal.Factorization.Rρk ρ k).eval (star s)
      = star ((Hyperlocal.Factorization.Rρk ρ k).eval s)

/--
RC inheritance off the zero set of the polynomial factor.
-/
lemma G_inherits_RC_off_zeros
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
    (HRC  : FunRC H)
    (RRC  : RC_R ρ k) :
    ∀ ⦃s : ℂ⦄, (Hyperlocal.Factorization.Rρk ρ k).eval (star s) ≠ 0
      → G (star s) = star (G s) := by
  intro s hRnz
  have eq_prod :
      (Hyperlocal.Factorization.Rρk ρ k).eval (star s) * G (star s)
        = (Hyperlocal.Factorization.Rρk ρ k).eval (star s) * star (G s) := by
    calc
      (Hyperlocal.Factorization.Rρk ρ k).eval (star s) * G (star s)
          = H (star s) := by rw [hfac]
      _   = star (H s) := by rw [HRC]
      _   = star ((Hyperlocal.Factorization.Rρk ρ k).eval s * G s) := by rw [hfac]
      _   = star (G s) * star ((Hyperlocal.Factorization.Rρk ρ k).eval s) := by rw [star_mul]
      -- This is the only change. We use `rw` with `mul_comm` to reorder the terms.
      _   = (Hyperlocal.Factorization.Rρk ρ k).eval (star s) * star (G s) := by rw [RRC, mul_comm]
  exact (Hyperlocal.Factorization.cancel_scalar_mul_left hRnz) eq_prod

-- This is the new lemma with its proof corrected.
/-- Disjunctive RC inheritance for `G`: either `G (star s) = star (G s)`,
    or the factor vanishes at `star s`. -/
lemma G_inherits_RC_or_zero
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
    (HRC  : FunRC H)
    (RRC  : RC_R ρ k) :
    ∀ s : ℂ, G (star s) = star (G s) ∨ (Hyperlocal.Factorization.Rρk ρ k).eval (star s) = 0 := by
  intro s
  -- We consider two cases based on whether the polynomial is zero or not.
  by_cases h_poly_zero : (Hyperlocal.Factorization.Rρk ρ k).eval (star s) = 0
  · -- Case 1: The polynomial is zero. We prove the right side of the 'or'.
    exact Or.inr h_poly_zero
  · -- Case 2: The polynomial is non-zero. We prove the left side of the 'or'.
    -- In this case, we can just use the previous lemma we already proved.
    have h_rc_inherits := G_inherits_RC_off_zeros hfac HRC RRC h_poly_zero
    exact Or.inl h_rc_inherits

end FactorizationRC
end Hyperlocal
