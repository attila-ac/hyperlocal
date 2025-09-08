-- formalisation/Hyperlocal/Factorization.lean
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Hyperlocal.Core
import Hyperlocal.MinimalModel

/-
  Minimal, modular factorisation layer.
-/

noncomputable section
open Polynomial

namespace Hyperlocal
namespace Factorization

/-- Quartet minimal model (alias to keep call-sites short). -/
abbrev Rρk (ρ : ℂ) (k : ℕ) : Polynomial ℂ :=
  Hyperlocal.MinimalModel.quartetPolyPow ρ k

/-- Evaluate `(X - z)^k` at `s` as `(s - z)^k`. -/
lemma eval_linPow (s z : ℂ) (k : ℕ) :
    (Hyperlocal.MinimalModel.linPow z k).eval s = (s - z)^k := by
  -- `linPow z k = (lin z)^k` and `(lin z).eval s = s - z`
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

/-- Cancel a nonzero complex scalar on the left (domain-style cancellation). -/
lemma cancel_scalar_mul_left {a b c : ℂ} (ha : a ≠ 0)
    (h : a * b = a * c) : b = c :=
  (mul_left_cancel₀ ha) h

/--
FE inheritance off the zero set of the polynomial factor.

If `H` satisfies FE, and `H = Rρk * G`, and `Rρk` itself respects FE at the level of values,
then for any `s` with `(Rρk ρ k).eval s ≠ 0` we have `G s = G (1 - s)`.
-/
lemma G_inherits_FE_off_zeros
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : FactorisedByQuartet H ρ k G)
    (HFE  : FunFE H)
    (RFE  : FE_R ρ k) :
    ∀ ⦃s : ℂ⦄, (Rρk ρ k).eval s ≠ 0 → G s = G (Hyperlocal.oneMinus s) := by
  intro s hR
  -- Name the factorisation equalities at s and (1 - s)
  have hfac_s   := hfac s
  have hfac_1ms := hfac (Hyperlocal.oneMinus s)
  have hH       := HFE s
  have hRFE     := RFE s
  -- Get: R(s)*G(s) = R(s)*G(1-s)
  have eq_prod :
      (Rρk ρ k).eval s * G s
        = (Rρk ρ k).eval s * G (Hyperlocal.oneMinus s) := by
    calc
      (Rρk ρ k).eval s * G s
          = H s := by simpa [hfac_s] using hfac_s.symm
      _   = H (Hyperlocal.oneMinus s) := hH
      _   = (Rρk ρ k).eval (Hyperlocal.oneMinus s) * G (Hyperlocal.oneMinus s) := by
              simpa [hfac_1ms]
      _   = (Rρk ρ k).eval s * G (Hyperlocal.oneMinus s) := by
              simpa [hRFE]
  -- Cancel the nonzero factor `R(s)`
  exact cancel_scalar_mul_left hR eq_prod

end Factorization
end Hyperlocal
