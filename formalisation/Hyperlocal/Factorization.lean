import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

import Hyperlocal.Core
import Hyperlocal.MinimalModel

/-
  Minimal, modular factorisation layer.
-/

noncomputable section
open Polynomial
open scoped Topology

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

/-!
### Quotient uniqueness off the zero set
-/

/-- If two functions factorise the same `H` by the same quartet polynomial, then they agree at any point where the polynomial factor is nonzero. -/
lemma factorisedByQuartet_eq_of_eval_ne_zero
    {H G G' : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac  : FactorisedByQuartet H ρ k G)
    (hfac' : FactorisedByQuartet H ρ k G')
    {z : ℂ} (hz : (Rρk ρ k).eval z ≠ 0) :
    G z = G' z := by
  have h1 := hfac z
  have h2 := hfac' z
  have hmul :
      (Rρk ρ k).eval z * G z = (Rρk ρ k).eval z * G' z := by
    calc
      (Rρk ρ k).eval z * G z = H z := by simpa [h1] using h1.symm
      _ = (Rρk ρ k).eval z * G' z := by simpa [h2] using h2
  exact cancel_scalar_mul_left hz hmul

/--
FE inheritance off the zero set of the polynomial factor.
-/
lemma G_inherits_FE_off_zeros
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : FactorisedByQuartet H ρ k G)
    (HFE  : FunFE H)
    (RFE  : FE_R ρ k) :
    ∀ ⦃s : ℂ⦄, (Rρk ρ k).eval s ≠ 0 → G s = G (Hyperlocal.oneMinus s) := by
  intro s hR
  have hfac_s   := hfac s
  have hfac_1ms := hfac (Hyperlocal.oneMinus s)
  have hH       := HFE s
  have hRFE     := RFE s
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
  exact cancel_scalar_mul_left hR eq_prod

/-!
### Local division off the zero set (the rigidity hammer)
-/

/-- Off the zero set, the quotient is locally equal to `H / R`. -/
lemma factorisedByQuartet_eventuallyEq_div
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : FactorisedByQuartet H ρ k G)
    {z : ℂ} (hz : (Rρk ρ k).eval z ≠ 0) :
    (∀ᶠ w in 𝓝 z, G w = H w / (Rρk ρ k).eval w) := by
  -- continuityAt ⇒ eventually nonzero near z (proved via `fun_prop` for snapshot robustness)
  have hne : ∀ᶠ w in 𝓝 z, (Rρk ρ k).eval w ≠ 0 := by
    have hcont : ContinuousAt (fun w : ℂ => (Rρk ρ k).eval w) z := by
      fun_prop
    simpa using hcont.eventually_ne hz

  refine hne.mono ?_
  intro w hw
  have h := hfac w
  -- from H w = R(w) * G w, rearrange to G w = H w / R(w)
  apply (eq_div_iff hw).2
  -- goal: G w * R(w) = H w
  calc
    G w * (Rρk ρ k).eval w
        = (Rρk ρ k).eval w * G w := by simpa [mul_comm]
    _ = H w := by simpa using h.symm

end Factorization
end Hyperlocal
