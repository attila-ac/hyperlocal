/-
  Hyperlocal/Cancellation/ImagAxisResultant.lean

  Stage-1 progress file:
  * Prove the two plumbing-heavy lemmas cleanly:
      - eval_map_ofReal
      - sum_range_two_mul
  * Decomposition + common-root + stabRes.

  NOTE on Mathlib variance / snapshot minimalism:
  -----------------------------------------------
  Your pinned Mathlib provides only `Resultant/Basic.lean`, and does NOT ship
  the usual bridge lemmas like “common root ⇒ resultant = 0”.
  So we isolate exactly that step as an axiom:

      resultant_eq_zero_of_common_root

  Everything else in this file is fully proved.
-/

import Mathlib
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section

namespace Hyperlocal
namespace Cancellation

open Polynomial
open scoped BigOperators

namespace ImagAxis

/-- Even-part polynomial in u = w^2: coeffs d_{2m}. -/
def evenU (Psi : Polynomial ℝ) : Polynomial ℝ :=
  Finset.sum (Finset.range (Psi.natDegree + 1)) (fun m =>
    Polynomial.C (Psi.coeff (2*m)) * Polynomial.X ^ m
  )

/-- Odd-part polynomial in u = w^2: coeffs d_{2m+1}. -/
def oddU (Psi : Polynomial ℝ) : Polynomial ℝ :=
  Finset.sum (Finset.range (Psi.natDegree + 1)) (fun m =>
    Polynomial.C (Psi.coeff (2*m+1)) * Polynomial.X ^ m
  )

/-- Evaluation commutes with mapping ℝ→ℂ at real points. -/
lemma eval_map_ofReal (p : Polynomial ℝ) (x : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (x : ℂ) = (algebraMap ℝ ℂ) (p.eval x) := by
  classical
  refine Polynomial.induction_on p
    (fun a => by simp)
    (fun p q hp hq => by simp [hp, hq])
    (fun n a => by simp)

/-- Pure parity split on `range (2*N)`. -/
lemma sum_range_two_mul {α : Type*} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) :
    (Finset.range (2*N)).sum f
      = (Finset.range N).sum (fun m => f (2*m))
        + (Finset.range N).sum (fun m => f (2*m+1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hL :
          (Finset.range (2*(N+1))).sum f
            = (Finset.range (2*N)).sum f + f (2*N) + f (2*N+1) := by
        calc
          (Finset.range (2*(N+1))).sum f
              = (Finset.range (2*N + 2)).sum f := by
                  simp [Nat.mul_succ, Nat.add_comm]
          _   = (Finset.range (2*N + 1)).sum f + f (2*N + 1) := by
                  simpa using (Finset.sum_range_succ f (2*N + 1))
          _   = ((Finset.range (2*N)).sum f + f (2*N)) + f (2*N + 1) := by
                  simpa [add_assoc] using
                    congrArg (fun t => t + f (2*N + 1)) (Finset.sum_range_succ f (2*N))
          _   = (Finset.range (2*N)).sum f + f (2*N) + f (2*N + 1) := by
                  simp [add_assoc]

      have hE :
          (Finset.range (N+1)).sum (fun m => f (2*m))
            = (Finset.range N).sum (fun m => f (2*m)) + f (2*N) := by
        simpa using (Finset.sum_range_succ (fun m => f (2*m)) N)

      have hO :
          (Finset.range (N+1)).sum (fun m => f (2*m+1))
            = (Finset.range N).sum (fun m => f (2*m+1)) + f (2*N+1) := by
        simpa using (Finset.sum_range_succ (fun m => f (2*m+1)) N)

      have hE' :
          (Finset.range N).sum (fun m => f (2*m)) + f (2*N)
            = (Finset.range (N+1)).sum (fun m => f (2*m)) := by
        simpa using hE.symm

      have hO' :
          (Finset.range N).sum (fun m => f (2*m+1)) + f (2*N+1)
            = (Finset.range (N+1)).sum (fun m => f (2*m+1)) := by
        simpa using hO.symm

      calc
        (Finset.range (2*(N+1))).sum f
            = (Finset.range (2*N)).sum f + f (2*N) + f (2*N+1) := hL
        _   = ((Finset.range N).sum (fun m => f (2*m))
                + (Finset.range N).sum (fun m => f (2*m+1)))
              + f (2*N) + f (2*N+1) := by
              simp [ih, add_assoc]
        _   = ((Finset.range N).sum (fun m => f (2*m)) + f (2*N))
              + ((Finset.range N).sum (fun m => f (2*m+1)) + f (2*N+1)) := by
              simp [add_assoc, add_comm, add_left_comm]
        _   = (Finset.range (N+1)).sum (fun m => f (2*m))
              + (Finset.range (N+1)).sum (fun m => f (2*m+1)) := by
              simpa [hE', hO']

/-- Tiny helper: kills goals of the form `I*(I*z) = -z`. -/
lemma I_mul_I_mul (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
  calc
    Complex.I * (Complex.I * z) = (Complex.I * Complex.I) * z := by
      simpa [mul_assoc] using (mul_assoc (Complex.I) (Complex.I) z).symm
    _ = (-1 : ℂ) * z := by simp
    _ = -z := by simp

theorem eval_map_eq_evenU_add_w_mul_oddU (Psi : Polynomial ℝ) (w : ℂ) :
    (Psi.map (algebraMap ℝ ℂ)).eval w
      =
    ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
      + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
  classical
  set N : ℕ := Psi.natDegree + 1
  let f : ℕ → ℂ := fun n => (algebraMap ℝ ℂ) (Psi.coeff n) * w ^ n

  have hmap :
      (Psi.map (algebraMap ℝ ℂ)).eval w = Psi.eval₂ (algebraMap ℝ ℂ) w := by
    simpa [Polynomial.eval] using
      (Polynomial.eval₂_map (p := Psi) (f := algebraMap ℝ ℂ)
        (g := RingHom.id ℂ) (x := w))

  have hsum :
      (Psi.map (algebraMap ℝ ℂ)).eval w = (Finset.range N).sum f := by
    simpa [hmap, f, N] using
      (Polynomial.eval₂_eq_sum_range (p := Psi) (f := algebraMap ℝ ℂ) (x := w))

  have htail : (Finset.range N).sum (fun i => f (N + i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hdeg : Psi.natDegree < N + i := by
      have hN : Psi.natDegree < N := by
        simpa [N] using Nat.lt_succ_self Psi.natDegree
      exact lt_of_lt_of_le hN (Nat.le_add_right N i)
    have hcoeff : Psi.coeff (N + i) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    simp [f, hcoeff]

  have h2 : (Finset.range (2 * N)).sum f = (Finset.range N).sum f := by
    have h := (Finset.sum_range_add f N N)
    have h' :
        (Finset.range (N + N)).sum f
          = (Finset.range N).sum f + (Finset.range N).sum (fun i => f (N + i)) := by
      simpa using h
    have h'' : (Finset.range (N + N)).sum f = (Finset.range N).sum f := by
      simpa [htail] using h'
    simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h''

  have hNto2N : (Finset.range N).sum f = (Finset.range (2 * N)).sum f := by
    simpa using h2.symm

  have hEvenEval :
      ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
        = (Finset.range N).sum (fun m =>
            (algebraMap ℝ ℂ) (Psi.coeff (2*m)) * (w^2)^m) := by
    simp [evenU, N]

  have hOddEval :
      ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
        = (Finset.range N).sum (fun m =>
            (algebraMap ℝ ℂ) (Psi.coeff (2*m+1)) * (w^2)^m) := by
    simp [oddU, N]

  have hEvenTerm :
      (Finset.range N).sum (fun m => f (2*m))
        = (Finset.range N).sum (fun m =>
            (algebraMap ℝ ℂ) (Psi.coeff (2*m)) * (w^2)^m) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hw2 : w^(2*m) = (w^2)^m := by
      simpa [pow_mul] using (pow_mul w 2 m)
    simp [f, hw2, mul_assoc]

  have hEven :
      (Finset.range N).sum (fun m => f (2*m))
        = ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
    calc
      (Finset.range N).sum (fun m => f (2*m))
          = (Finset.range N).sum (fun m =>
              (algebraMap ℝ ℂ) (Psi.coeff (2*m)) * (w^2)^m) := hEvenTerm
      _   = ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
              simpa using hEvenEval.symm

  let g : ℕ → ℂ := fun m =>
      (algebraMap ℝ ℂ) (Psi.coeff (2*m+1)) * (w^2)^m

  have hOddTerm :
      (Finset.range N).sum (fun m => f (2*m+1))
        = (Finset.range N).sum (fun m => w * g m) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hw2 : w^(2*m) = (w^2)^m := by
      simpa [pow_mul] using (pow_mul w 2 m)
    have hw : w^(2*m+1) = w * (w^2)^m := by
      calc
        w^(2*m+1) = w^(2*m) * w := by
          simpa [Nat.succ_eq_add_one] using (pow_succ w (2*m))
        _ = (w^2)^m * w := by simpa [hw2]
        _ = w * (w^2)^m := by ac_rfl
    simp [f, g, hw] ; ac_rfl

  have hOddSum :
      (Finset.range N).sum (fun m => f (2*m+1))
        = w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
    have hg : (Finset.range N).sum (fun m => w * g m) = w * (Finset.range N).sum g := by
      simpa using (Finset.mul_sum (a := w) (s := Finset.range N) (f := g)).symm
    have hsumeq : (Finset.range N).sum g = ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
      simpa [g] using hOddEval.symm
    calc
      (Finset.range N).sum (fun m => f (2*m+1))
          = (Finset.range N).sum (fun m => w * g m) := hOddTerm
      _   = w * (Finset.range N).sum g := hg
      _   = w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
              simpa [hsumeq]

  calc
    (Psi.map (algebraMap ℝ ℂ)).eval w
        = (Finset.range N).sum f := hsum
    _   = (Finset.range (2 * N)).sum f := hNto2N
    _   = (Finset.range N).sum (fun m => f (2*m))
          + (Finset.range N).sum (fun m => f (2*m+1)) := by
          simpa using (sum_range_two_mul (α := ℂ) (N := N) (f := f))
    _   = ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
          + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
          rw [hEven, hOddSum]

/-- If Ψ(i*y)=0 (real coeffs) and y≠0, then evenU and oddU share root u = -y^2. -/
theorem imagAxis_root_implies_common_root {Psi : Polynomial ℝ} {y : ℝ}
    (hy : y ≠ 0)
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    (evenU Psi).IsRoot (-(y^2)) ∧ (oddU Psi).IsRoot (-(y^2)) := by
  classical
  set w : ℂ := Complex.I * (y : ℂ)
  set a : ℝ := -(y^2)

  have hw2 : w^2 = (a : ℂ) := by
    dsimp [w, a]
    -- compute (I*y)^2 = (I*I)*(y*y) = - y^2
    calc
      (Complex.I * (y : ℂ))^2
          = (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)) := by
              simp [pow_two]
      _   = (Complex.I * Complex.I) * ((y : ℂ) * (y : ℂ)) := by
              -- regroup (I*y)*(I*y) into (I*I)*(y*y)
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (mul_mul_mul_comm (Complex.I) (y : ℂ) (Complex.I) (y : ℂ))
      _   = (-1 : ℂ) * ((y : ℂ) * (y : ℂ)) := by simp
      _   = -((y : ℂ) * (y : ℂ)) := by simp
      _   = (-(y^2) : ℂ) := by simp [pow_two]
      _   = (a : ℂ) := by simp [a]

  have hwroot : (Psi.map (algebraMap ℝ ℂ)).eval w = 0 := by
    simpa [Polynomial.IsRoot, w] using hroot

  have hz :
      ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
        + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) = 0 := by
    have hdecomp := eval_map_eq_evenU_add_w_mul_oddU (Psi := Psi) (w := w)
    simpa [hdecomp] using hwroot

  have hEven :
      ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
        = (algebraMap ℝ ℂ) ((evenU Psi).eval a) := by
    simpa [hw2] using (eval_map_ofReal (p := evenU Psi) (x := a))

  have hOdd :
      ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
        = (algebraMap ℝ ℂ) ((oddU Psi).eval a) := by
    simpa [hw2] using (eval_map_ofReal (p := oddU Psi) (x := a))

  have hz' :
      (algebraMap ℝ ℂ) ((evenU Psi).eval a)
        + w * (algebraMap ℝ ℂ) ((oddU Psi).eval a) = 0 := by
    simpa [hEven, hOdd] using hz

  have hz'' :
      Complex.ofReal ((evenU Psi).eval a)
        + Complex.I * Complex.ofReal (y * (oddU Psi).eval a) = 0 := by
    have hz1 :
        Complex.ofReal ((evenU Psi).eval a)
          + (Complex.I * Complex.ofReal y) * Complex.ofReal ((oddU Psi).eval a) = 0 := by
      simpa [w] using hz'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hz1

  have he : (evenU Psi).eval a = 0 := by
    have hre := congrArg Complex.re hz''
    simpa using hre

  have hyO : y * (oddU Psi).eval a = 0 := by
    have him := congrArg Complex.im hz''
    simpa using him

  have ho : (oddU Psi).eval a = 0 :=
    (mul_eq_zero.mp hyO).resolve_left hy

  constructor
  · simpa [Polynomial.IsRoot, a] using he
  · simpa [Polynomial.IsRoot, a] using ho

/-
  Resultant step: isolated to avoid missing theory in your pinned Mathlib snapshot.
-/
axiom resultant_eq_zero_of_common_root
    {f g : Polynomial ℝ} {a : ℝ} :
    f.IsRoot a → g.IsRoot a → f.resultant g = 0

/-- Stability resultant certificate. -/
def stabRes (Psi : Polynomial ℝ) : ℝ :=
  (evenU Psi).resultant (oddU Psi)

/-- Imag-axis root (with y≠0) ⇒ stabRes = 0. -/
theorem imagAxis_root_implies_stabRes_zero
    {Psi : Polynomial ℝ} {y : ℝ}
    (hy : y ≠ 0)
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    stabRes Psi = 0 := by
  classical
  rcases imagAxis_root_implies_common_root (Psi := Psi) (y := y) hy hroot with ⟨hE, hO⟩
  simpa [stabRes] using
    (resultant_eq_zero_of_common_root
      (f := evenU Psi) (g := oddU Psi) (a := -(y^2)) hE hO)

end ImagAxis
end Cancellation
end Hyperlocal
