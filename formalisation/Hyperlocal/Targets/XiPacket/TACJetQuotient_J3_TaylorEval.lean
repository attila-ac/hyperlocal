/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_TaylorEval.lean

  Taylor → J3 semantics (the *correct* place where truncation is exact):

    J3 := ℂ[w]/(w^3)

  For an entire function `f : ℂ → ℂ`, the germ

      f (c + δ + w) mod w^3

  is exactly determined by the coefficients

      f (c+δ), f'(c+δ), f''(c+δ)/2

  because `w^3 = 0`.

  This file defines the J3-valued “Taylor-evaluate then truncate in w” object,
  and proves it agrees with the canonical order-2 jet polynomial at the shifted point.

  IMPORTANT:
  This does *not* imply your ℂ-level `JetShiftExactEq` statement.
  It is the honest quotient-semantics fact you can actually discharge from Mathlib.
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_Algebra
import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_Binomial
import Hyperlocal.Targets.XiPacket.TACJetShiftExactEq3_J3

import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex
open scoped BigOperators

namespace J3

/-- The usual Taylor coefficient at `c`: `(n!)⁻¹ * iteratedDeriv n f c`. -/
def taylorCoeff (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n f c

/-- The `w^0` coefficient when expanding `f (c + δ + w)` around `c` and truncating in `w`. -/
def coeff0 (f : ℂ → ℂ) (c δ : ℂ) : ℂ :=
  ∑' n, (taylorCoeff f c n) * δ ^ n

/-- The `w^1` coefficient: Taylor series for `deriv f` at `c`, evaluated at `δ`. -/
def coeff1 (f : ℂ → ℂ) (c δ : ℂ) : ℂ :=
  ∑' n, ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n (fun z => deriv f z) c * δ ^ n

/-- The `w^2` coefficient: Taylor series for `deriv (deriv f)` at `c`, evaluated at `δ`. -/
def coeff2 (f : ℂ → ℂ) (c δ : ℂ) : ℂ :=
  ∑' n, ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n (fun z => deriv (deriv f) z) c * δ ^ n

/-- The J3-valued truncated germ: `a0 + a1*w + (a2/2)*w^2`. -/
def taylorJet2J3 (f : ℂ → ℂ) (c δ : ℂ) : J3 :=
  jet2 (coeff0 f c δ) (coeff1 f c δ) ((coeff2 f c δ) / (2 : ℂ))

/-- `w^0` coefficient equals `f (c+δ)` by Mathlib Taylor (entire). -/
lemma coeff0_eq_of_entire'
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c δ : ℂ) :
    coeff0 f c δ = f (c + δ) := by
  have h := Complex.taylorSeries_eq_of_entire' (f := f) hf (c := c) (z := c + δ)
  simpa [coeff0, taylorCoeff, mul_assoc, mul_left_comm, mul_comm] using h

/-- `w^1` coefficient equals `(deriv f) (c+δ)` by applying Taylor to `deriv f`. -/
lemma coeff1_eq_of_entire'
    (f : ℂ → ℂ)
    (hf1 : Differentiable ℂ (fun z => deriv f z))
    (c δ : ℂ) :
    coeff1 f c δ = deriv f (c + δ) := by
  have h :=
    Complex.taylorSeries_eq_of_entire'
      (f := fun z => deriv f z) hf1 (c := c) (z := c + δ)
  simpa [coeff1, mul_assoc, mul_left_comm, mul_comm] using h

/-- `w^2` coefficient equals `(deriv (deriv f)) (c+δ)` by applying Taylor to `deriv (deriv f)`. -/
lemma coeff2_eq_of_entire'
    (f : ℂ → ℂ)
    (hf2 : Differentiable ℂ (fun z => deriv (deriv f) z))
    (c δ : ℂ) :
    coeff2 f c δ = deriv (deriv f) (c + δ) := by
  have h :=
    Complex.taylorSeries_eq_of_entire'
      (f := fun z => deriv (deriv f) z) hf2 (c := c) (z := c + δ)
  simpa [coeff2, mul_assoc, mul_left_comm, mul_comm] using h

/--
Main theorem: the J3-truncated germ agrees with the canonical J3 jet polynomial at `c+δ`.

This is the exact (and provable) “truncate in `w`” semantics.
-/
theorem taylorJet2J3_eq_J3Jet2_of_entire'
    (f : ℂ → ℂ)
    (hf0 : Differentiable ℂ f)
    (hf1 : Differentiable ℂ (fun z => deriv f z))
    (hf2 : Differentiable ℂ (fun z => deriv (deriv f) z))
    (c δ : ℂ) :
    taylorJet2J3 f c δ = J3Jet2 f (c + δ) := by
  have h0 : coeff0 f c δ = f (c + δ) :=
    coeff0_eq_of_entire' (f := f) hf0 (c := c) (δ := δ)
  have h1 : coeff1 f c δ = deriv f (c + δ) :=
    coeff1_eq_of_entire' (f := f) hf1 (c := c) (δ := δ)
  have h2 : coeff2 f c δ = deriv (deriv f) (c + δ) :=
    coeff2_eq_of_entire' (f := f) hf2 (c := c) (δ := δ)
  simp [taylorJet2J3, J3Jet2, jetCoeff0, jetCoeff1, jetCoeff2, h0, h1, h2]

end J3

end TAC
end XiPacket
end Targets
end Hyperlocal
