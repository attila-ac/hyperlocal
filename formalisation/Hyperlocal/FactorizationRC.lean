-- Add at the top of the file if not already present:
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Star.Basic
import Hyperlocal.Core
import Hyperlocal.MinimalModel

noncomputable section
open Polynomial

namespace Hyperlocal
namespace Factorization

/-- Quartet minimal model (alias). -/
abbrev Rρk (ρ : ℂ) (k : ℕ) : Polynomial ℂ :=
  Hyperlocal.MinimalModel.quartetPolyPow ρ k

/-- Evaluation of a power of a linear factor. -/
lemma eval_linPow (s z : ℂ) (k : ℕ) :
    (Hyperlocal.MinimalModel.linPow z k).eval s = (s - z)^k := by
  simp [Hyperlocal.MinimalModel.linPow, Hyperlocal.MinimalModel.lin, eval_pow]

/-- Abstract factorisation: `H(s) = (Rρk ρ k).eval s * G(s)` for all `s`. -/
def FactorisedByQuartet (H : ℂ → ℂ) (ρ : ℂ) (k : ℕ) (G : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, H s = (Rρk ρ k).eval s * G s

/-- FE on scalar functions (same convention as in `Core`). -/
def FunFE (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, F s = F (Hyperlocal.oneMinus s)

/-- Value-level FE hypothesis for the quartet polynomial factor. -/
def FE_R (ρ : ℂ) (k : ℕ) : Prop :=
  ∀ s : ℂ, (Rρk ρ k).eval (Hyperlocal.oneMinus s) = (Rρk ρ k).eval s

/-- RC on scalar functions (same convention as in `Core`). -/
def FunRC (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, F (star s) = star (F s)

/-- Value-level RC hypothesis for the quartet polynomial factor. -/
def RC_R (ρ : ℂ) (k : ℕ) : Prop :=
  ∀ s : ℂ, (Rρk ρ k).eval (star s) = star ((Rρk ρ k).eval s)

/-- Cancel a nonzero complex scalar on the left. -/
lemma cancel_scalar_mul_left {a b c : ℂ} (ha : a ≠ 0)
    (h : a * b = a * c) : b = c :=
  (mul_left_inj' ha).mp h

/-- FE inheritance off the zero set of the polynomial factor. -/
lemma G_inherits_FE_off_zeros
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : FactorisedByQuartet H ρ k G)
    (HFE  : FunFE H)
    (RFE  : FE_R ρ k) :
    ∀ ⦃s : ℂ⦄, (Rρk ρ k).eval s ≠ 0 → G s = G (Hyperlocal.oneMinus s) := by
  intro s hR
  have : (Rρk ρ k).eval s * G s = (Rρk ρ k).eval s * G (Hyperlocal.oneMinus s) := by
    calc
      (Rρk ρ k).eval s * G s
          = H s := by simpa [FactorisedByQuartet] using (hfac s)
      _   = H (Hyperlocal.oneMinus s) := by simpa [FunFE] using (HFE s)
      _   = (Rρk ρ k).eval (Hyperlocal.oneMinus s) * G (Hyperlocal.oneMinus s) := by
              simpa [FactorisedByQuartet] using (hfac (Hyperlocal.oneMinus s))
      _   = (Rρk ρ k).eval s * G (Hyperlocal.oneMinus s) := by simpa [FE_R] using (RFE s)
  exact cancel_scalar_mul_left hR this

/-- RC inheritance off the zero set of the polynomial factor. -/
lemma G_inherits_RC_off_zeros
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : FactorisedByQuartet H ρ k G)
    (HRC  : FunRC H)
    (RRC  : RC_R ρ k) :
    ∀ ⦃s : ℂ⦄, (Rρk ρ k).eval s ≠ 0 → G (star s) = star (G s) := by
  intro s hR
  have : (Rρk ρ k).eval (star s) * G (star s) = (Rρk ρ k).eval (star s) * star (G s) := by
    calc
      (Rρk ρ k).eval (star s) * G (star s)
          = H (star s) := hfac (star s)
      _   = star (H s) := HRC s
      _   = star ((Rρk ρ k).eval s * G s) := by rw [hfac s]
      _   = star (G s) * star ((Rρk ρ k).eval s) := by simp [star_mul]
      _   = star (G s) * (Rρk ρ k).eval (star s) := by rw [RRC s]
      _   = (Rρk ρ k).eval (star s) * star (G s) := by rw [mul_comm]
  exact cancel_scalar_mul_left (by rwa [← RRC s, ← star_eq_zero]) this


end Factorization
end Hyperlocal
