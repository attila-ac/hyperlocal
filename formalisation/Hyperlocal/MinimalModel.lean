import Mathlib.Algebra.Polynomial.Basic
import Hyperlocal.Core
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
open Polynomial

namespace Hyperlocal.MinimalModel

/-- Linear factor `X - C z`. -/
def lin (z : ℂ) : Polynomial ℂ := X - C z

/-- Power of a linear factor, i.e. encodes multiplicity `k` at `z`. -/
def linPow (z : ℂ) (k : ℕ) : Polynomial ℂ := (lin z) ^ k

/-- `X ↦ 1 - X` as a polynomial. -/
def oneMinusX : Polynomial ℂ := C (1 : ℂ) - X

/-- Basic quartic (simple roots). -/
def quartetPoly (ρ : ℂ) : Polynomial ℂ :=
  lin ρ * lin (star ρ) * lin (Hyperlocal.oneMinus ρ) * lin (Hyperlocal.oneMinus (star ρ))

/-- Quartic with uniform multiplicity `k` on the quartet. -/
def quartetPolyPow (ρ : ℂ) (k : ℕ) : Polynomial ℂ :=
  linPow ρ k *
  linPow (star ρ) k *
  linPow (Hyperlocal.oneMinus ρ) k *
  linPow (Hyperlocal.oneMinus (star ρ)) k

/-- Composition with `X ↦ 1 - X` sends `X - C z` to `-(X - C (1 - z))`. -/
lemma comp_oneMinusX (z : ℂ) :
    (lin z).comp oneMinusX = - lin (Hyperlocal.oneMinus z) := by
  -- Unfold and let `simp` compute the composition on `X` and `C _`;
  -- no big rewrite chains.
  unfold lin oneMinusX
  -- (X - C z).comp (C 1 - X) = (C 1 - X) - C z = C (1 - z) - X = -(X - C (1 - z))
  simp [Hyperlocal.oneMinus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Powers: `((lin z).comp (1 - X))^k = (-1)^k * (lin (1 - z))^k`. -/
lemma comp_oneMinusX_pow (z : ℂ) (k : ℕ) :
    ((lin z).comp oneMinusX) ^ k
      = (-1 : Polynomial ℂ) ^ k * (lin (Hyperlocal.oneMinus z)) ^ k := by
  -- step 1: rewrite the composition itself
  have hcomp : (lin z).comp oneMinusX = - lin (Hyperlocal.oneMinus z) :=
    comp_oneMinusX z
  rw [hcomp]
  -- step 2: rewrite `-a` as `(-1) * a`
  have hneg' :
      (-1 : Polynomial ℂ) * lin (Hyperlocal.oneMinus z)
        = - lin (Hyperlocal.oneMinus z) :=
    neg_one_mul (lin (Hyperlocal.oneMinus z))
  have hneg :
      - lin (Hyperlocal.oneMinus z)
        = (-1 : Polynomial ℂ) * lin (Hyperlocal.oneMinus z) :=
    hneg'.symm
  rw [hneg]
  -- step 3: pull the power through the product
  rw [mul_pow]   -- gives `(-1)^k * (lin (1 - z))^k`

/-- Convenient lemma: evaluation of a linear factor. -/
lemma eval_lin (s z : ℂ) : (lin z).eval s = s - z := by
  -- (X - C z).eval s = s - z
  simp [lin]

/-- Convenient lemma: derivative of a linear factor evaluates to `1`. -/
lemma eval_deriv_lin (s z : ℂ) :
    (Polynomial.derivative (lin z)).eval s = (1 : ℂ) := by
  -- derivative (X - C z) = 1 - 0 = 1
  simp [lin]

/-- Product rule specialized to four factors, evaluated at a point where the first factor vanishes.
Only the term with the derivative of the first factor survives. -/
lemma eval_derivative_mul4
    (A B C D : Polynomial ℂ) (x : ℂ)
    (hA : A.eval x = 0) :
    (Polynomial.derivative (A * B * C * D)).eval x
      = (Polynomial.derivative A).eval x * B.eval x * C.eval x * D.eval x := by
  -- Expand derivative ((A*B*C)'*D + (A*B*C)*D')
  -- and ((A*B)'*C + (A*B)*C'), and (A'*B + A*B')
  -- Then evaluate and kill all terms containing A.eval x = 0.
  -- `simp` handles pushing `eval` through +/* and uses `hA` to drop terms.
  simp [Polynomial.derivative_mul, mul_comm, mul_left_comm, mul_assoc, hA]

/-- **Simple (k = 1) model:** the derivative of the quartet polynomial at `ρ`
is the product of the three differences from `ρ` to the other members of the quartet. -/
lemma quartet_derivative_at_seed (ρ : ℂ) :
    (Polynomial.derivative (quartetPoly ρ)).eval ρ
      = (ρ - star ρ) * (ρ - Hyperlocal.oneMinus ρ) * (ρ - Hyperlocal.oneMinus (star ρ)) := by
  -- Name the factors
  set A := lin ρ with hAdef
  set B := lin (star ρ) with hBdef
  set C := lin (Hyperlocal.oneMinus ρ) with hCdef
  set D := lin (Hyperlocal.oneMinus (star ρ)) with hDdef
  have hP : quartetPoly ρ = A * B * C * D := by
    simp [quartetPoly, hAdef, hBdef, hCdef, hDdef]
  have hA0 : A.eval ρ = 0 := by simp [hAdef, lin, eval_lin]
  -- Product rule at ρ: only the A' term survives
  have H :=
    eval_derivative_mul4 A B C D ρ hA0
  -- Rewrite everything and drop the leading `1` coming from A'
  have H' :
      (Polynomial.derivative (quartetPoly ρ)).eval ρ
        = (1 : ℂ) * (ρ - star ρ) * (ρ - Hyperlocal.oneMinus ρ)
            * (ρ - Hyperlocal.oneMinus (star ρ)) := by
    simpa [ hP,
            hAdef, hBdef, hCdef, hDdef,
            eval_deriv_lin, eval_lin,
            Hyperlocal.oneMinus,
            mul_comm, mul_left_comm, mul_assoc ] using H
  simpa [one_mul] using H'

/-- **Multiplicity (uniform k ≥ 2):** for any `m`, the first derivative of the
power-model with exponent `m + 2` vanishes at the seed `ρ`. -/
lemma quartetPow_derivative_at_seed_is_zero_twoPlus (ρ : ℂ) (m : ℕ) :
    (Polynomial.derivative (quartetPolyPow ρ (m + 2))).eval ρ = 0 := by
  classical
  -- Abbreviations
  set A := lin ρ with hAdef
  set B := lin (star ρ) with hBdef
  set C := lin (Hyperlocal.oneMinus ρ) with hCdef
  set D := lin (Hyperlocal.oneMinus (star ρ)) with hDdef
  have hP :
      quartetPolyPow ρ (m + 2) = A^(m+2) * B^(m+2) * C^(m+2) * D^(m+2) := by
    simp [quartetPolyPow, linPow, hAdef, hBdef, hCdef, hDdef]
  have hA0 : A.eval ρ = 0 := by simp [hAdef, lin, eval_lin]
  -- A^(m+2) evaluates to 0 at ρ (since A.eval ρ = 0 and exponent ≥ 2)
  have hA0pow : (A^(m+2)).eval ρ = 0 := by
    -- (A^(m+2)).eval ρ = ((A^m) * (A^2)).eval ρ = (A^m).eval ρ * (A.eval ρ)^2 = 0
    have : A^(m+2) = A^m * A^2 := by
      simp [pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc]
    simpa [ this, Polynomial.eval_mul, pow_two, hA0,
            mul_comm, mul_left_comm, mul_assoc ]  -- (A.eval ρ)^2 = 0
  -- Product rule for four factors with the first vanishing at ρ
  have H :=
    eval_derivative_mul4 (A^(m+2)) (B^(m+2)) (C^(m+2)) (D^(m+2)) ρ hA0pow
  -- Now expand derivative of the power and evaluate
  -- derivative (A^(m+2)) = (m+2) * A^(m+1) * derivative A
  -- Evaluating gives a factor (A.eval ρ)^(m+1) = 0, so the whole term is 0.
  simpa [ hP,
          Polynomial.derivative_pow, Polynomial.eval_mul, Polynomial.eval_pow,
          hAdef, hBdef, hCdef, hDdef,
          eval_deriv_lin, eval_lin,
          Hyperlocal.oneMinus,
          mul_comm, mul_left_comm, mul_assoc ] using H

/-- Wrapper in the original statement form. -/
lemma quartetPow_derivative_at_seed_is_zero
    (ρ : ℂ) {k : ℕ} (hk : 2 ≤ k) :
    (Polynomial.derivative (quartetPolyPow ρ k)).eval ρ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk  -- k = 2 + m
  -- turn `2 + m` into `m + 2` for the previous lemma
  simpa [Nat.add_comm] using quartetPow_derivative_at_seed_is_zero_twoPlus ρ m

end Hyperlocal.MinimalModel
