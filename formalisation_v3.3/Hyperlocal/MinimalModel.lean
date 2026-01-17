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
  unfold lin oneMinusX
  simp [Hyperlocal.oneMinus, sub_eq_add_neg]
  ring

/-- Powers: `((lin z).comp (1 - X))^k = (-1)^k * (lin (1 - z))^k`. -/
lemma comp_oneMinusX_pow (z : ℂ) (k : ℕ) :
    ((lin z).comp oneMinusX) ^ k
      = (-1 : Polynomial ℂ) ^ k * (lin (Hyperlocal.oneMinus z)) ^ k := by
  have hcomp : (lin z).comp oneMinusX = - lin (Hyperlocal.oneMinus z) :=
    comp_oneMinusX z
  rw [hcomp, neg_eq_neg_one_mul, mul_pow]

/-- Evaluation of a linear factor. -/
lemma eval_lin (s z : ℂ) : (lin z).eval s = s - z := by
  simp [lin]

/-- Derivative of a linear factor evaluates to `1`. -/
lemma eval_deriv_lin (s z : ℂ) :
    (Polynomial.derivative (lin z)).eval s = (1 : ℂ) := by
  simp [lin]

/-- Product rule specialized to four factors, evaluated at a point where the first factor vanishes. -/
lemma eval_derivative_mul4
    (A B C D : Polynomial ℂ) (x : ℂ)
    (hA : A.eval x = 0) :
    (Polynomial.derivative (A * B * C * D)).eval x
      = (Polynomial.derivative A).eval x * B.eval x * C.eval x * D.eval x := by
  simp [Polynomial.derivative_mul, mul_comm, mul_left_comm, mul_assoc, hA]

/-- **Simple (k = 1) model:** derivative of the quartet polynomial at `ρ`. -/
lemma quartet_derivative_at_seed (ρ : ℂ) :
    (Polynomial.derivative (quartetPoly ρ)).eval ρ
      = (ρ - star ρ) * (ρ - Hyperlocal.oneMinus ρ) * (ρ - Hyperlocal.oneMinus (star ρ)) := by
  set A := lin ρ with hAdef
  set B := lin (star ρ) with hBdef
  set C := lin (Hyperlocal.oneMinus ρ) with hCdef
  set D := lin (Hyperlocal.oneMinus (star ρ)) with hDdef
  have hP : quartetPoly ρ = A * B * C * D := by
    simp [quartetPoly, hAdef, hBdef, hCdef, hDdef]
  have hA0 : A.eval ρ = 0 := by
    simp [hAdef, lin, eval_lin]
  have H :=
    eval_derivative_mul4 A B C D ρ hA0
  have H' :
      (Polynomial.derivative (quartetPoly ρ)).eval ρ
        = (1 : ℂ) * (ρ - star ρ) * (ρ - Hyperlocal.oneMinus ρ)
            * (ρ - Hyperlocal.oneMinus (star ρ)) := by
    simpa [hP, hAdef, hBdef, hCdef, hDdef, eval_deriv_lin, eval_lin, Hyperlocal.oneMinus] using H
  simpa [one_mul] using H'

/-- **Multiplicity (uniform k ≥ 2):** first derivative of the power-model vanishes at `ρ`. -/
lemma quartetPow_derivative_at_seed_is_zero_twoPlus (ρ : ℂ) (m : ℕ) :
    (Polynomial.derivative (quartetPolyPow ρ (m + 2))).eval ρ = 0 := by
  classical
  set A := lin ρ with hAdef
  set B := lin (star ρ) with hBdef
  set C := lin (Hyperlocal.oneMinus ρ) with hCdef
  set D := lin (Hyperlocal.oneMinus (star ρ)) with hDdef
  have hP :
      quartetPolyPow ρ (m + 2) = A^(m+2) * B^(m+2) * C^(m+2) * D^(m+2) := by
    simp [quartetPolyPow, linPow, hAdef, hBdef, hCdef, hDdef]
  have hA0 : A.eval ρ = 0 := by
    simp [hAdef, lin, eval_lin]
  have hA0pow : (A^(m+2)).eval ρ = 0 := by
    simp [Polynomial.eval_pow, hA0]
  have H :=
    eval_derivative_mul4 (A^(m+2)) (B^(m+2)) (C^(m+2)) (D^(m+2)) ρ hA0pow
  have hAderiv0 : (Polynomial.derivative (A^(m+2))).eval ρ = 0 := by
    simp [Polynomial.derivative_pow, Polynomial.eval_pow, hA0]
  have : (Polynomial.derivative ((A^(m+2)) * (B^(m+2)) * (C^(m+2)) * (D^(m+2)))).eval ρ = 0 := by
    simpa [hAderiv0, mul_comm, mul_left_comm, mul_assoc] using H
  simpa [hP] using this

/-- Wrapper: if `k ≥ 2` then the first derivative at `ρ` vanishes. -/
lemma quartetPow_derivative_at_seed_is_zero
    (ρ : ℂ) {k : ℕ} (hk : 2 ≤ k) :
    (Polynomial.derivative (quartetPolyPow ρ k)).eval ρ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk  -- k = 2 + m
  simpa [Nat.add_comm] using quartetPow_derivative_at_seed_is_zero_twoPlus ρ m

end Hyperlocal.MinimalModel
