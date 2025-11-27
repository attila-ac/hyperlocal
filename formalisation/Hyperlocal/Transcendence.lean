/-
  Hyperlocal/Transcendence.lean

  Minimal transcendence step:
  If H is transcendental and H = R · G with R polynomial (as a function),
  then G is transcendental.

  This file is import-light and avoids referencing Factorization/ρ entirely.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical

namespace Hyperlocal
namespace Transcendence

/-- `f` is a polynomial function iff there exists a polynomial `p` with `f z = p.eval z`. -/
def IsPolynomialFun (f : ℂ → ℂ) : Prop :=
  ∃ p : Polynomial ℂ, f = fun z => p.eval z

/-- `f` is transcendental iff it is *not* a polynomial function. -/
def Transcendental (f : ℂ → ℂ) : Prop :=
  ¬ IsPolynomialFun f

/-- Any fixed polynomial evaluated at `z` is (trivially) a polynomial function. -/
lemma isPolynomialFun_eval (p : Polynomial ℂ) :
    IsPolynomialFun (fun z : ℂ => p.eval z) :=
  ⟨p, rfl⟩

/-- Polynomial functions are closed under pointwise multiplication. -/
lemma IsPolynomialFun.mul
    {f g : ℂ → ℂ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun (fun z => f z * g z) := by
  rcases hf with ⟨p, rfl⟩
  rcases hg with ⟨q, rfl⟩
  refine ⟨p * q, ?_⟩
  funext z
  simp [Polynomial.eval_mul]

/-- If `H = R * G`, `H` is transcendental and `R` is a polynomial function,
    then `G` is transcendental. -/
lemma transcendental_of_factor
    {H G R : ℂ → ℂ}
    (hH : Transcendental H)
    (hR : IsPolynomialFun R)
    (hfac : ∀ z, H z = R z * G z) :
    Transcendental G := by
  intro hG
  have hRG : IsPolynomialFun (fun z => R z * G z) := hR.mul hG
  rcases hRG with ⟨p, hp⟩
  have : IsPolynomialFun H := by
    refine ⟨p, ?_⟩
    funext z
    -- use hp pointwise at z, then chain with hfac z
    calc
      H z = R z * G z := hfac z
      _   = p.eval z  := by
        simpa using congrArg (fun f : ℂ → ℂ => f z) hp
  exact hH this

/-- Handy specialization that avoids any `Factorization` names:
    if `H z = (p.eval z) * G z` for some polynomial `p`, and `H` is transcendental,
    then `G` is transcendental. -/
lemma G_transcendental_of_eval_poly_factor
    {H G : ℂ → ℂ} (p : Polynomial ℂ)
    (hH : Transcendental H)
    (hfac : ∀ z, H z = (p.eval z) * G z) :
    Transcendental G := by
  have hR : IsPolynomialFun (fun z : ℂ => p.eval z) := isPolynomialFun_eval p
  exact transcendental_of_factor hH hR hfac

end Transcendence
end Hyperlocal
