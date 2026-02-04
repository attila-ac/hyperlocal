/-
  Hyperlocal/Transport/PrimeSineRescue.lean

  Step 1 (pure algebra): “functional elimination lemma” via a 3×3 determinant.

  Given three vectors u0, uc, us : Fin 3 → ℝ, define the scalar functional

      ell(v) := det [u0, uc, v]

  (i.e. determinant of the 3×3 matrix whose columns are u0, uc, v).

  Then:
    • ell u0 = 0
    • ell uc = 0
    • ell us = det [u0, uc, us] =: κ

  And if a vector up decomposes as
      up = u0 + a • uc + b • us
  and ell(up)=0, then automatically
      κ * b = 0
  (hence if κ ≠ 0 then b = 0).

  A trig-specialization is provided as a corollary:
      up = u0 + cos θ • uc + sin θ • us, ell(up)=0  ⇒  κ * sin θ = 0.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped BigOperators

/-- Base matrix with first two columns `u0`,`uc` and third column `0`. -/
def baseMat (u0 uc : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if j = (0 : Fin 3) then u0 i
    else if j = (1 : Fin 3) then uc i
    else 0

/-- The 3×3 matrix whose columns are `u0`, `uc`, `v`. -/
def colsMat (u0 uc v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (baseMat u0 uc).updateCol (2 : Fin 3) v

/-- The determinant functional ℓ(v) := det[u0, uc, v]. -/
def ell (u0 uc : Fin 3 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  (colsMat u0 uc v).det

/-- κ := det[u0, uc, us]. -/
def kappa (u0 uc us : Fin 3 → ℝ) : ℝ :=
  ell u0 uc us

/-- Column-0 of `baseMat` is exactly `u0`. -/
lemma baseMat_col0 (u0 uc : Fin 3 → ℝ) :
    (fun i => baseMat u0 uc i (0 : Fin 3)) = u0 := by
  funext i
  simp [baseMat]

/-- Column-1 of `baseMat` is exactly `uc`. -/
lemma baseMat_col1 (u0 uc : Fin 3 → ℝ) :
    (fun i => baseMat u0 uc i (1 : Fin 3)) = uc := by
  funext i
  simp [baseMat]

/-- ℓ is additive in its argument (linearity in the 3rd column). -/
lemma ell_add (u0 uc v w : Fin 3 → ℝ) :
    ell u0 uc (v + w) = ell u0 uc v + ell u0 uc w := by
  classical
  -- det(M.updateCol j (v+w)) = det(M.updateCol j v) + det(M.updateCol j w)
  simpa [ell, colsMat] using
    (Matrix.det_updateCol_add (M := baseMat u0 uc) (j := (2 : Fin 3)) v w)

/-- ℓ respects scalar multiplication in its argument (linearity in the 3rd column). -/
lemma ell_smul (u0 uc : Fin 3 → ℝ) (a : ℝ) (v : Fin 3 → ℝ) :
    ell u0 uc (a • v) = a * ell u0 uc v := by
  classical
  -- det(M.updateCol j (a • v)) = a * det(M.updateCol j v)
  simpa [ell, colsMat] using
    (Matrix.det_updateCol_smul (M := baseMat u0 uc) (j := (2 : Fin 3)) a v)

/-- ℓ(u0)=0 since columns 0 and 2 coincide. -/
lemma ell_u0 (u0 uc : Fin 3 → ℝ) :
    ell u0 uc u0 = 0 := by
  classical
  have hcol : (fun i => baseMat u0 uc i (0 : Fin 3)) = u0 := baseMat_col0 u0 uc
  -- det(M.updateCol j (col i)) = 0 for i ≠ j
  have h :=
    (Matrix.det_updateCol_eq_zero (M := baseMat u0 uc)
      (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide))
  simpa [ell, colsMat, hcol] using h

/-- ℓ(uc)=0 since columns 1 and 2 coincide. -/
lemma ell_uc (u0 uc : Fin 3 → ℝ) :
    ell u0 uc uc = 0 := by
  classical
  have hcol : (fun i => baseMat u0 uc i (1 : Fin 3)) = uc := baseMat_col1 u0 uc
  have h :=
    (Matrix.det_updateCol_eq_zero (M := baseMat u0 uc)
      (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide))
  simpa [ell, colsMat, hcol] using h

/-- By definition, ℓ(us) is κ. -/
lemma ell_us_eq_kappa (u0 uc us : Fin 3 → ℝ) :
    ell u0 uc us = kappa u0 uc us := rfl

/-
Core elimination (“rescue”) lemma:
If up = u0 + a•uc + b•us and ℓ(up)=0 then κ*b=0.
-/
theorem kappa_mul_coeff_eq_zero_of_ell_eq_zero
    (u0 uc us up : Fin 3 → ℝ) (a b : ℝ)
    (hup : up = u0 + a • uc + b • us)
    (hEll : ell u0 uc up = 0) :
    kappa u0 uc us * b = 0 := by
  classical
  -- Rewrite ℓ(up)=0 using the decomposition
  have h0 : ell u0 uc (u0 + a • uc + b • us) = 0 := by
    simpa [hup] using hEll
  -- Reassociate to use ell_add twice
  have h0' : ell u0 uc (u0 + (a • uc + b • us)) = 0 := by
    simpa [add_assoc] using h0

  have hu0 : ell u0 uc u0 = 0 := ell_u0 u0 uc
  have huc : ell u0 uc uc = 0 := ell_uc u0 uc

  -- Expand ℓ(u0 + (a•uc + b•us))
  have hsplit_outer :
      ell u0 uc (u0 + (a • uc + b • us))
        = ell u0 uc u0 + ell u0 uc (a • uc + b • us) := by
    simpa using (ell_add u0 uc u0 (a • uc + b • us))

  have hsplit_inner :
      ell u0 uc (a • uc + b • us)
        = ell u0 uc (a • uc) + ell u0 uc (b • us) := by
    simpa using (ell_add u0 uc (a • uc) (b • us))

  have ha : ell u0 uc (a • uc) = a * ell u0 uc uc := by
    simpa using (ell_smul u0 uc a uc)

  have hb : ell u0 uc (b • us) = b * ell u0 uc us := by
    simpa using (ell_smul u0 uc b us)

  -- Turn h0' into a scalar equation and simplify u0/uc terms away
  have : ell u0 uc u0 + (a * ell u0 uc uc + b * ell u0 uc us) = 0 := by
    -- use hsplit_outer, then rewrite the inner part, then rewrite smul parts
    have : ell u0 uc (u0 + (a • uc + b • us))
              = ell u0 uc u0 + (a * ell u0 uc uc + b * ell u0 uc us) := by
      calc
        ell u0 uc (u0 + (a • uc + b • us))
            = ell u0 uc u0 + ell u0 uc (a • uc + b • us) := hsplit_outer
        _ = ell u0 uc u0 + (ell u0 uc (a • uc) + ell u0 uc (b • us)) := by
              simp [hsplit_inner, add_assoc]
        _ = ell u0 uc u0 + (a * ell u0 uc uc + b * ell u0 uc us) := by
              simp [ha, hb, add_assoc]
    -- substitute into h0'
    simpa [this] using h0'

  -- now simplify with hu0,huc and extract the b*κ term
  have hbκ : b * ell u0 uc us = 0 := by
    -- from: 0 + (a*0 + b*ℓ(us)) = 0
    simpa [hu0, huc, add_assoc, add_left_comm, add_comm] using this

  -- rewrite κ and swap order to κ*b
  -- hbκ is b * ℓ(us) = 0, so κ*b = 0 by commutativity
  simpa [kappa, mul_comm, mul_left_comm, mul_assoc] using hbκ

/-- If κ ≠ 0, the previous lemma forces the coefficient `b` to be zero. -/
theorem coeff_eq_zero_of_ell_eq_zero
    (u0 uc us up : Fin 3 → ℝ) (a b : ℝ)
    (hup : up = u0 + a • uc + b • us)
    (hEll : ell u0 uc up = 0)
    (hk : kappa u0 uc us ≠ 0) :
    b = 0 := by
  have hk0 : kappa u0 uc us * b = 0 :=
    kappa_mul_coeff_eq_zero_of_ell_eq_zero u0 uc us up a b hup hEll
  -- mul_eq_zero: κ*b=0 ⇒ κ=0 or b=0
  have : kappa u0 uc us = 0 ∨ b = 0 := by
    simpa [mul_eq_zero] using (mul_eq_zero.mp hk0)
  cases this with
  | inl hκ => exact (hk hκ).elim
  | inr hb => exact hb

/-
Trig specialization (your exact “prime rescue” shape):
If up = u0 + cos θ • uc + sin θ • us and ℓ(up)=0, then κ * sin θ = 0.
-/
theorem kappa_mul_sin_eq_zero_of_ell_eq_zero
    (u0 uc us up : Fin 3 → ℝ) (θ : ℝ)
    (hup : up = u0 + (Real.cos θ) • uc + (Real.sin θ) • us)
    (hEll : ell u0 uc up = 0) :
    kappa u0 uc us * Real.sin θ = 0 := by
  simpa using
    (kappa_mul_coeff_eq_zero_of_ell_eq_zero
      (u0 := u0) (uc := uc) (us := us) (up := up)
      (a := Real.cos θ) (b := Real.sin θ) hup hEll)

end Transport
end Hyperlocal
