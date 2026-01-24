/-
  Hyperlocal/Cancellation/ImagAxisResultant.lean

  Imaginary-axis root detection via parity splitting + resultant.

  We avoid the `∑ x in s, ...` notation to prevent scope/notation issues.
-/

import Mathlib

noncomputable section

namespace Hyperlocal
namespace Cancellation

open Polynomial

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

/-- Parity decomposition over ℂ (after mapping ℝ→ℂ). -/
theorem eval_map_eq_evenU_add_w_mul_oddU (Psi : Polynomial ℝ) (w : ℂ) :
    (Psi.map (algebraMap ℝ ℂ)).eval w
      =
    ((evenU Psi).map (algebraMap ℝ ℂ)).eval (w^2)
      + w * ((oddU Psi).map (algebraMap ℝ ℂ)).eval (w^2) := by
  -- Fill later:
  -- expand Psi via coeff-sum, regroup even/odd indices
  sorry

/-- If Psi(i*y)=0 (real coeffs), then evenU and oddU share root u = -y^2. -/
theorem imagAxis_root_implies_common_root {Psi : Polynomial ℝ} {y : ℝ}
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    (evenU Psi).IsRoot (-(y^2)) ∧ (oddU Psi).IsRoot (-(y^2)) := by
  -- Use parity decomposition at w = I*y and (I*y)^2 = -(y^2).
  -- Then split real/imag parts.
  sorry

/-- If f and g share a root, resultant f g = 0. -/
theorem resultant_eq_zero_of_common_root
    {f g : Polynomial ℝ} {a : ℝ}
    (hf : f.IsRoot a) (hg : g.IsRoot a) :
    f.resultant g = 0 := by
  -- Hook: Bezout identity for resultants
  -- `Polynomial.exists_mul_add_mul_eq_C_resultant` is the standard lemma.
  sorry

/-- Stability resultant certificate. -/
def stabRes (Psi : Polynomial ℝ) : ℝ :=
  (evenU Psi).resultant (oddU Psi)

/-- Imag-axis root ⇒ stabRes = 0. -/
theorem imagAxis_root_implies_stabRes_zero
    {Psi : Polynomial ℝ} {y : ℝ}
    (hroot : (Psi.map (algebraMap ℝ ℂ)).IsRoot (Complex.I * (y : ℂ))) :
    stabRes Psi = 0 := by
  have hcommon := imagAxis_root_implies_common_root (Psi := Psi) (y := y) hroot
  -- apply resultant_eq_zero_of_common_root at a = -(y^2)
  -- unfold stabRes
  sorry

end ImagAxis
end Cancellation
end Hyperlocal
