/-
  Hyperlocal/Cancellation/ImagAxisResultant.lean

  Stage-1 progress file:
  * Prove the two plumbing-heavy lemmas cleanly:
      - eval_map_ofReal
      - sum_range_two_mul
  * Decomposition + common-root + stabRes.

  IMPORTANT correction (2026-03-14):
  ----------------------------------
  In the pinned Mathlib snapshot, the raw statement

      f.IsRoot a -> g.IsRoot a -> f.resultant g = 0

  is false when f = g = 0, because `resultant 0 0 = 1`
  (the determinant of a 0x0 Sylvester matrix).

  So this file replaces the old axiom by the honest guarded theorem:
  a common root forces resultant zero provided `f ≠ 0 ∨ g ≠ 0`.

  Correspondingly, the final `stabRes` theorem also carries the explicit
  nontriviality guard on the even/odd split.
-/

import Mathlib
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section

namespace Hyperlocal
namespace Cancellation

open Polynomial
open Matrix
open scoped BigOperators

namespace ImagAxis

/-- Even-part polynomial in u = w^2: coeffs d_{2m}. -/
def evenU (Psi : Polynomial ℝ) : Polynomial ℝ :=
  Finset.sum (Finset.range (Psi.natDegree + 1)) (fun m =>
    Polynomial.C (Psi.coeff (2 * m)) * Polynomial.X ^ m
  )

/-- Odd-part polynomial in u = w^2: coeffs d_{2m+1}. -/
def oddU (Psi : Polynomial ℝ) : Polynomial ℝ :=
  Finset.sum (Finset.range (Psi.natDegree + 1)) (fun m =>
    Polynomial.C (Psi.coeff (2 * m + 1)) * Polynomial.X ^ m
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
    (Finset.range (2 * N)).sum f
      = (Finset.range N).sum (fun m => f (2 * m))
        + (Finset.range N).sum (fun m => f (2 * m + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hL :
          (Finset.range (2 * (N + 1))).sum f
            = (Finset.range (2 * N)).sum f + f (2 * N) + f (2 * N + 1) := by
        calc
          (Finset.range (2 * (N + 1))).sum f
              = (Finset.range (2 * N + 2)).sum f := by
                  simp [Nat.mul_succ, Nat.add_comm]
          _   = (Finset.range (2 * N + 1)).sum f + f (2 * N + 1) := by
                  simpa using (Finset.sum_range_succ f (2 * N + 1))
          _   = ((Finset.range (2 * N)).sum f + f (2 * N)) + f (2 * N + 1) := by
                  simpa [add_assoc] using
                    congrArg (fun t => t + f (2 * N + 1)) (Finset.sum_range_succ f (2 * N))
          _   = (Finset.range (2 * N)).sum f + f (2 * N) + f (2 * N + 1) := by
                  simp [add_assoc]

      have hE :
          (Finset.range (N + 1)).sum (fun m => f (2 * m))
            = (Finset.range N).sum (fun m => f (2 * m)) + f (2 * N) := by
        simpa using (Finset.sum_range_succ (fun m => f (2 * m)) N)

      have hO :
          (Finset.range (N + 1)).sum (fun m => f (2 * m + 1))
            = (Finset.range N).sum (fun m => f (2 * m + 1)) + f (2 * N + 1) := by
        simpa using (Finset.sum_range_succ (fun m => f (2 * m + 1)) N)

      have hE' :
          (Finset.range N).sum (fun m => f (2 * m)) + f (2 * N)
            = (Finset.range (N + 1)).sum (fun m => f (2 * m)) := by
        simpa using hE.symm

      have hO' :
          (Finset.range N).sum (fun m => f (2 * m + 1)) + f (2 * N + 1)
            = (Finset.range (N + 1)).sum (fun m => f (2 * m + 1)) := by
        simpa using hO.symm

      calc
        (Finset.range (2 * (N + 1))).sum f
            = (Finset.range (2 * N)).sum f + f (2 * N) + f (2 * N + 1) := hL
        _   = ((Finset.range N).sum (fun m => f (2 * m))
                + (Finset.range N).sum (fun m => f (2 * m + 1)))
              + f (2 * N) + f (2 * N + 1) := by
              simp [ih, add_assoc]
        _   = ((Finset.range N).sum (fun m => f (2 * m)) + f (2 * N))
              + ((Finset.range N).sum (fun m => f (2 * m + 1)) + f (2 * N + 1)) := by
              simp [add_assoc, add_comm, add_left_comm]
        _   = (Finset.range (N + 1)).sum (fun m => f (2 * m))
              + (Finset.range (N + 1)).sum (fun m => f (2 * m + 1)) := by
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
    ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
      + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
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
      ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
        = (Finset.range N).sum (fun m =>
            (algebraMap ℝ ℂ) (Psi.coeff (2 * m)) * (w ^ 2) ^ m) := by
    simp [evenU, N]

  have hOddEval :
      ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
        = (Finset.range N).sum (fun m =>
            (algebraMap ℝ ℂ) (Psi.coeff (2 * m + 1)) * (w ^ 2) ^ m) := by
    simp [oddU, N]

  have hEvenTerm :
      (Finset.range N).sum (fun m => f (2 * m))
        = (Finset.range N).sum (fun m =>
            (algebraMap ℝ ℂ) (Psi.coeff (2 * m)) * (w ^ 2) ^ m) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hw2 : w ^ (2 * m) = (w ^ 2) ^ m := by
      simpa [pow_mul] using (pow_mul w 2 m)
    simp [f, hw2, mul_assoc]

  have hEven :
      (Finset.range N).sum (fun m => f (2 * m))
        = ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
    calc
      (Finset.range N).sum (fun m => f (2 * m))
          = (Finset.range N).sum (fun m =>
              (algebraMap ℝ ℂ) (Psi.coeff (2 * m)) * (w ^ 2) ^ m) := hEvenTerm
      _   = ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
              simpa using hEvenEval.symm

  let g : ℕ → ℂ := fun m =>
      (algebraMap ℝ ℂ) (Psi.coeff (2 * m + 1)) * (w ^ 2) ^ m

  have hOddTerm :
      (Finset.range N).sum (fun m => f (2 * m + 1))
        = (Finset.range N).sum (fun m => w * g m) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hw2 : w ^ (2 * m) = (w ^ 2) ^ m := by
      simpa [pow_mul] using (pow_mul w 2 m)
    have hw : w ^ (2 * m + 1) = w * (w ^ 2) ^ m := by
      calc
        w ^ (2 * m + 1) = w ^ (2 * m) * w := by
          simpa [Nat.succ_eq_add_one] using (pow_succ w (2 * m))
        _ = (w ^ 2) ^ m * w := by simpa [hw2]
        _ = w * (w ^ 2) ^ m := by ac_rfl
    simp [f, g, hw]
    ac_rfl

  have hOddSum :
      (Finset.range N).sum (fun m => f (2 * m + 1))
        = w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
    have hg : (Finset.range N).sum (fun m => w * g m) = w * (Finset.range N).sum g := by
      simpa using (Finset.mul_sum (a := w) (s := Finset.range N) (f := g)).symm
    have hsumeq : (Finset.range N).sum g = ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
      simpa [g] using hOddEval.symm
    calc
      (Finset.range N).sum (fun m => f (2 * m + 1))
          = (Finset.range N).sum (fun m => w * g m) := hOddTerm
      _   = w * (Finset.range N).sum g := hg
      _   = w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
              simpa [hsumeq]

  calc
    (Psi.map (algebraMap ℝ ℂ)).eval w
        = (Finset.range N).sum f := hsum
    _   = (Finset.range (2 * N)).sum f := hNto2N
    _   = (Finset.range N).sum (fun m => f (2 * m))
          + (Finset.range N).sum (fun m => f (2 * m + 1)) := by
          simpa using (sum_range_two_mul (α := ℂ) (N := N) (f := f))
    _   = ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
          + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) := by
          rw [hEven, hOddSum]

/-- If Ψ(i*y)=0 (real coeffs) and y≠0, then evenU and oddU share root u = -y^2. -/
theorem imagAxis_root_implies_common_root {Psi : Polynomial ℝ} {y : ℝ}
    (hy : y ≠ 0)
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    (evenU Psi).IsRoot (-(y ^ 2)) ∧ (oddU Psi).IsRoot (-(y ^ 2)) := by
  classical
  set w : ℂ := Complex.I * (y : ℂ)
  set a : ℝ := -(y ^ 2)

  have hw2 : w ^ 2 = (a : ℂ) := by
    dsimp [w, a]
    calc
      (Complex.I * (y : ℂ)) ^ 2
          = (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)) := by
              simp [pow_two]
      _   = (Complex.I * Complex.I) * ((y : ℂ) * (y : ℂ)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (mul_mul_mul_comm (Complex.I) (y : ℂ) (Complex.I) (y : ℂ))
      _   = (-1 : ℂ) * ((y : ℂ) * (y : ℂ)) := by simp
      _   = -((y : ℂ) * (y : ℂ)) := by simp
      _   = (-(y ^ 2) : ℂ) := by simp [pow_two]
      _   = (a : ℂ) := by simp [a]

  have hwroot : (Psi.map (algebraMap ℝ ℂ)).eval w = 0 := by
    simpa [Polynomial.IsRoot, w] using hroot

  have hz :
      ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
        + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2) = 0 := by
    have hdecomp := eval_map_eq_evenU_add_w_mul_oddU (Psi := Psi) (w := w)
    simpa [hdecomp] using hwroot

  have hEven :
      ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
        = (algebraMap ℝ ℂ) ((evenU Psi).eval a) := by
    simpa [hw2] using (eval_map_ofReal (p := evenU Psi) (x := a))

  have hOdd :
      ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w ^ 2)
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

def rootVec (a : ℝ) (N : ℕ) : Fin N → ℝ := fun i => a ^ (i : ℕ)

lemma rootVec_ne_zero (a : ℝ) {N : ℕ} (hN : 0 < N) :
    rootVec a N ≠ 0 := by
  intro h
  have h0 := congrArg (fun v => v ⟨0, hN⟩) h
  simpa [rootVec] using h0

lemma natDegree_pos_of_ne_zero_of_isRoot
    {p : Polynomial ℝ} {a : ℝ}
    (hp0 : p ≠ 0) (hroot : p.IsRoot a) :
    0 < p.natDegree := by
  by_contra hdeg
  have hdeg0 : p.natDegree = 0 := by
    omega
  have hconst : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  have heval0 : p.eval a = 0 := by
    simpa [Polynomial.IsRoot] using hroot
  rw [hconst, Polynomial.eval_C] at heval0
  have hcoeff0 : p.coeff 0 = 0 := by
    simpa using heval0
  apply hp0
  simpa [hcoeff0] using hconst

lemma sum_Icc_shift (j m : ℕ) (φ : ℕ → ℝ) :
    (Finset.Icc j (j + m)).sum φ
      = (Finset.range (m + 1)).sum (fun k => φ (j + k)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        (Finset.Icc j (j + (m + 1))).sum φ
            = (Finset.Icc j (j + m)).sum φ + φ (j + (m + 1)) := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (Finset.sum_Icc_succ_top (f := φ) (a := j) (b := j + m) (by omega))
        _ = (Finset.range (m + 1)).sum (fun k => φ (j + k)) + φ (j + (m + 1)) := by
              rw [ih]
        _ = (Finset.range (m + 2)).sum (fun k => φ (j + k)) := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Finset.sum_range_succ (fun k => φ (j + k)) (m + 1)).symm

lemma sylvester_left_block_eval
    {f g : Polynomial ℝ} {a : ℝ}
    (j : Fin g.natDegree) :
    ((rootVec a (g.natDegree + f.natDegree)) ᵥ*
        (Polynomial.sylvester f g f.natDegree g.natDegree))
        (Fin.castAdd f.natDegree j)
      =
    a ^ (j : ℕ) * f.eval a := by
  classical
  rw [Matrix.vecMul, dotProduct, Polynomial.sylvester]
  simp only [Matrix.of_apply, rootVec, Fin.addCases_left]

  have hsumFin :
      (∑ x : Fin (g.natDegree + f.natDegree),
          a ^ (x : ℕ) *
            (if (x : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree) then
              f.coeff ((x : ℕ) - (j : ℕ))
            else 0))
        =
      (Finset.range (g.natDegree + f.natDegree)).sum
        (fun i : ℕ =>
          a ^ i *
            (if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree) then
              f.coeff (i - (j : ℕ))
            else 0)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun i : ℕ =>
          a ^ i *
            (if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree) then
              f.coeff (i - (j : ℕ))
            else 0))
        (n := g.natDegree + f.natDegree))

  rw [hsumFin]

  have hite :
      (Finset.range (g.natDegree + f.natDegree)).sum
        (fun i : ℕ =>
          a ^ i *
            (if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree) then
              f.coeff (i - (j : ℕ))
            else 0))
      =
      (Finset.range (g.natDegree + f.natDegree)).sum
        (fun i : ℕ =>
          if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree) then
            a ^ i * f.coeff (i - (j : ℕ))
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hi' : i ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree)
    · simp [hi']
    · simp [hi']

  rw [hite, ← Finset.sum_filter]

  have hupper : (j : ℕ) + f.natDegree < g.natDegree + f.natDegree := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Nat.add_lt_add_right j.is_lt f.natDegree

  have hfilter :
      (Finset.range (g.natDegree + f.natDegree)).filter
        (fun i : ℕ => i ∈ Set.Icc (j : ℕ) ((j : ℕ) + f.natDegree))
        =
      Finset.Icc (j : ℕ) ((j : ℕ) + f.natDegree) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Set.mem_Icc] at hi
      rw [Finset.mem_Icc]
      exact hi.2
    · intro hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_filter, Finset.mem_range, Set.mem_Icc]
      exact ⟨lt_of_le_of_lt hi.2 hupper, hi⟩

  rw [hfilter, sum_Icc_shift]

  calc
    (Finset.range (f.natDegree + 1)).sum
        (fun k =>
          a ^ ((j : ℕ) + k) *
            f.coeff (((j : ℕ) + k) - (j : ℕ)))
      =
    (Finset.range (f.natDegree + 1)).sum
        (fun k => a ^ (j : ℕ) * (f.coeff k * a ^ k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [pow_add, Nat.add_sub_cancel_left, mul_assoc, mul_left_comm, mul_comm]
  _ = a ^ (j : ℕ) *
        ((Finset.range (f.natDegree + 1)).sum (fun k => f.coeff k * a ^ k)) := by
      rw [Finset.mul_sum]
  _ = a ^ (j : ℕ) * f.eval a := by
      congr 1
      symm
      simpa using (Polynomial.eval_eq_sum_range (p := f) (x := a))

lemma sylvester_right_block_eval
    {f g : Polynomial ℝ} {a : ℝ}
    (j : Fin f.natDegree) :
    ((rootVec a (g.natDegree + f.natDegree)) ᵥ*
        (Polynomial.sylvester f g f.natDegree g.natDegree))
        (Fin.natAdd g.natDegree j)
      =
    a ^ (j : ℕ) * g.eval a := by
  classical
  rw [Matrix.vecMul, dotProduct, Polynomial.sylvester]
  simp only [Matrix.of_apply, rootVec, Fin.addCases_right]

  have hsumFin :
      (∑ x : Fin (g.natDegree + f.natDegree),
          a ^ (x : ℕ) *
            (if (x : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree) then
              g.coeff ((x : ℕ) - (j : ℕ))
            else 0))
        =
      (Finset.range (g.natDegree + f.natDegree)).sum
        (fun i : ℕ =>
          a ^ i *
            (if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree) then
              g.coeff (i - (j : ℕ))
            else 0)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun i : ℕ =>
          a ^ i *
            (if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree) then
              g.coeff (i - (j : ℕ))
            else 0))
        (n := g.natDegree + f.natDegree))

  rw [hsumFin]

  have hite :
      (Finset.range (g.natDegree + f.natDegree)).sum
        (fun i : ℕ =>
          a ^ i *
            (if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree) then
              g.coeff (i - (j : ℕ))
            else 0))
      =
      (Finset.range (g.natDegree + f.natDegree)).sum
        (fun i : ℕ =>
          if i ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree) then
            a ^ i * g.coeff (i - (j : ℕ))
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hi' : i ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree)
    · simp [hi']
    · simp [hi']

  rw [hite, ← Finset.sum_filter]

  have hupper : (j : ℕ) + g.natDegree < g.natDegree + f.natDegree := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Nat.add_lt_add_left j.is_lt g.natDegree

  have hfilter :
      (Finset.range (g.natDegree + f.natDegree)).filter
        (fun i : ℕ => i ∈ Set.Icc (j : ℕ) ((j : ℕ) + g.natDegree))
        =
      Finset.Icc (j : ℕ) ((j : ℕ) + g.natDegree) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Set.mem_Icc] at hi
      rw [Finset.mem_Icc]
      exact hi.2
    · intro hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_filter, Finset.mem_range, Set.mem_Icc]
      exact ⟨lt_of_le_of_lt hi.2 hupper, hi⟩

  rw [hfilter, sum_Icc_shift]

  calc
    (Finset.range (g.natDegree + 1)).sum
        (fun k =>
          a ^ ((j : ℕ) + k) *
            g.coeff (((j : ℕ) + k) - (j : ℕ)))
      =
    (Finset.range (g.natDegree + 1)).sum
        (fun k => a ^ (j : ℕ) * (g.coeff k * a ^ k)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [pow_add, Nat.add_sub_cancel_left, mul_assoc, mul_left_comm, mul_comm]
  _ = a ^ (j : ℕ) *
        ((Finset.range (g.natDegree + 1)).sum (fun k => g.coeff k * a ^ k)) := by
      rw [Finset.mul_sum]
  _ = a ^ (j : ℕ) * g.eval a := by
      congr 1
      symm
      simpa using (Polynomial.eval_eq_sum_range (p := g) (x := a))

theorem resultant_eq_zero_of_common_root
    {f g : Polynomial ℝ} {a : ℝ}
    (hfg : f ≠ 0 ∨ g ≠ 0) :
    f.IsRoot a → g.IsRoot a → f.resultant g = 0 := by
  intro hf hg
  classical
  let v : Fin (g.natDegree + f.natDegree) → ℝ :=
    rootVec a (g.natDegree + f.natDegree)

  have hv : v ≠ 0 := by
    apply rootVec_ne_zero
    cases hfg with
    | inl hf0 =>
        have hfdeg : 0 < f.natDegree :=
          natDegree_pos_of_ne_zero_of_isRoot (p := f) (a := a) hf0 hf
        omega
    | inr hg0 =>
        have hgdeg : 0 < g.natDegree :=
          natDegree_pos_of_ne_zero_of_isRoot (p := g) (a := a) hg0 hg
        omega

  have hvm :
      v ᵥ* (Polynomial.sylvester f g f.natDegree g.natDegree) = 0 := by
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro j'
      have hf0 : f.eval a = 0 := by
        simpa [Polynomial.IsRoot] using hf
      simpa [v, hf0] using
        (sylvester_left_block_eval (f := f) (g := g) (a := a) j')
    · intro j'
      have hg0 : g.eval a = 0 := by
        simpa [Polynomial.IsRoot] using hg
      simpa [v, hg0] using
        (sylvester_right_block_eval (f := f) (g := g) (a := a) j')

  have hdet :
      (Polynomial.sylvester f g f.natDegree g.natDegree).det = 0 := by
    exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv, hvm⟩

  simpa [Polynomial.resultant] using hdet

/-- Stability resultant certificate. -/
def stabRes (Psi : Polynomial ℝ) : ℝ :=
  (evenU Psi).resultant (oddU Psi)

/--
Imag-axis root (with y≠0) implies vanishing of the stability resultant,
provided the even/odd split is not simultaneously zero.

This explicit guard is necessary in the pinned snapshot because
`resultant 0 0 = 1`.
-/
theorem imagAxis_root_implies_stabRes_zero
    {Psi : Polynomial ℝ} {y : ℝ}
    (hsplit : evenU Psi ≠ 0 ∨ oddU Psi ≠ 0)
    (hy : y ≠ 0)
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    stabRes Psi = 0 := by
  classical
  rcases imagAxis_root_implies_common_root (Psi := Psi) (y := y) hy hroot with ⟨hE, hO⟩
  simpa [stabRes] using
    (resultant_eq_zero_of_common_root
      (f := evenU Psi) (g := oddU Psi) (a := -(y ^ 2)) hsplit hE hO)

end ImagAxis
end Cancellation
end Hyperlocal
