/-
  Hyperlocal/Cancellation/ImagAxisResultant.lean

  Stage-1 progress file:
  * Prove the two plumbing-heavy lemmas cleanly:
      - eval_map_ofReal
      - sum_range_two_mul
  * Leave the downstream decomposition/resultant theorems as TODO/sorry for now.
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
  -- In your version, the third case is monomials: `C a * X^n`.
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
                  simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
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
              -- no `congrArg2` needed in your version
              simpa [hE', hO']

/-- Tiny helper: kills goals of the form `I*(I*z) = -z`. -/
lemma I_mul_I_mul (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
  calc
    Complex.I * (Complex.I * z) = (Complex.I * Complex.I) * z := by
      -- force reassociation in the right direction
      simpa [mul_assoc] using (mul_assoc (Complex.I) (Complex.I) z).symm
    _ = (-1 : ℂ) * z := by simp
    _ = -z := by simp

/- =========================================================
   Downstream theorems (Stage-2+): keep as TODO for now
   ========================================================= -/

/-- Parity decomposition over ℂ (after mapping ℝ→ℂ). -/
theorem eval_map_eq_evenU_add_w_mul_oddU (Psi : Polynomial ℝ) (w : ℂ) :
    (Psi.map (algebraMap ℝ ℂ)).eval w
      =
    ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
      + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
  sorry

/-- If Ψ(i*y)=0 (real coeffs) and y≠0, then evenU and oddU share root u = -y^2. -/
theorem imagAxis_root_implies_common_root {Psi : Polynomial ℝ} {y : ℝ}
    (hy : y ≠ 0)
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    (evenU Psi).IsRoot (-(y^2)) ∧ (oddU Psi).IsRoot (-(y^2)) := by
  sorry

/-- If f and g share a root, resultant f g = 0. -/
theorem resultant_eq_zero_of_common_root
    {f g : Polynomial ℝ} {a : ℝ}
    (hf : f.IsRoot a) (hg : g.IsRoot a) :
    f.resultant g = 0 := by
  sorry

/-- Stability resultant certificate. -/
def stabRes (Psi : Polynomial ℝ) : ℝ :=
  (evenU Psi).resultant (oddU Psi)

/-- Imag-axis root (with y≠0) ⇒ stabRes = 0. -/
theorem imagAxis_root_implies_stabRes_zero
    {Psi : Polynomial ℝ} {y : ℝ}
    (hy : y ≠ 0)
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    stabRes Psi = 0 := by
  sorry

end ImagAxis
end Cancellation
end Hyperlocal
