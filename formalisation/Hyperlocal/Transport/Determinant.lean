/-
  Hyperlocal/Transport/Determinant.lean

  Determinant helper layer.

  Provides:
    Transport.ell_eq_zero_of_depRow3

  Pure algebra:
    (nonzero left-kernel row on 3 columns) ⇒ det = 0
  specialized to your `Transport.ell` / `Transport.colsMat` definitions.
-/

import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Transport
namespace Transport

open scoped BigOperators

/-- Local replacement for the missing `Matrix.det_eq_zero_of_mulVec_eq_zero` in your Mathlib pin. -/
private lemma det_eq_zero_of_mulVec_eq_zero_fin3
    (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (hv : A.mulVec v = 0) (hnz : v ≠ 0) :
    Matrix.det A = 0 := by
  classical

  -- Multiply `A*v=0` by `adj(A)` on the left.
  have hAdj : (Matrix.adjugate A).mulVec (A.mulVec v) = 0 := by
    simpa [hv]

  -- Rewrite as `((adj A) * A) * v = 0`.
  have hMul : ((Matrix.adjugate A) * A).mulVec v = 0 := by
    -- `mulVec_mulVec : (B * A).mulVec v = B.mulVec (A.mulVec v)`
    simpa [Matrix.mulVec_mulVec] using hAdj

  -- Use `adj(A) * A = det(A) • 1`.
  have hDetMat : (A.det • (1 : Matrix (Fin 3) (Fin 3) ℝ)).mulVec v = 0 := by
    simpa [Matrix.adjugate_mul] using hMul


  -- Simplify to `det(A) • v = 0`.
  have hDetVec : (A.det • v) = 0 := by
    simpa [Matrix.smul_mulVec_assoc, Matrix.one_mulVec] using hDetMat

  -- Pick a coordinate where `v i ≠ 0`, then `det(A)=0`.
  rcases Function.ne_iff.mp hnz with ⟨i, hi⟩
  have : A.det * v i = 0 := by
    have := congrArg (fun f => f i) hDetVec
    simpa [Pi.smul_apply, smul_eq_mul] using this
  exact (mul_eq_zero.mp this).resolve_right hi

/--
If a nonzero real row `c : Fin 3 → ℝ` annihilates three real Window-3 vectors
`u0, uc, up`, then the transported determinant `ell u0 uc up` vanishes.

Used as:
(row stencil on 3 columns) ⇒ (left kernel nontrivial) ⇒ det = 0.
-/
theorem ell_eq_zero_of_depRow3
    (u0 uc up : Fin 3 → ℝ) (c : Fin 3 → ℝ)
    (hc : c ≠ 0)
    (h0  : (∑ i : Fin 3, c i * u0 i) = 0)
    (hc0 : (∑ i : Fin 3, c i * uc i) = 0)
    (hp  : (∑ i : Fin 3, c i * up i) = 0) :
    ell u0 uc up = 0 := by
  classical

  -- Matrix with columns u0, uc, up (same object used by `ell`).
  let M : Matrix (Fin 3) (Fin 3) ℝ := colsMat u0 uc up

  -- Match `mulVec` convention: `∑ i, (col i) * c i`.
  have h0'  : (∑ i : Fin 3, (u0 i) * c i) = 0 := by simpa [mul_comm] using h0
  have hc0' : (∑ i : Fin 3, (uc i) * c i) = 0 := by simpa [mul_comm] using hc0
  have hp'  : (∑ i : Fin 3, (up i) * c i) = 0 := by simpa [mul_comm] using hp

  -- Left-kernel statement as `(Mᵀ).mulVec c = 0`.
  have hmul : (Matrix.transpose M).mulVec c = 0 := by
    ext j
    fin_cases j
    · simpa [M, Matrix.mulVec, Matrix.transpose_apply, colsMat] using h0'
    · simpa [M, Matrix.mulVec, Matrix.transpose_apply, colsMat] using hc0'
    · simpa [M, Matrix.mulVec, Matrix.transpose_apply, colsMat] using hp'

  -- Nontrivial kernel ⇒ determinant zero (on transpose), hence also on M.
  have hdetT : Matrix.det (Matrix.transpose M) = 0 :=
    det_eq_zero_of_mulVec_eq_zero_fin3 (A := Matrix.transpose M) (v := c) hmul hc

  have hdet : Matrix.det M = 0 := by
    simpa [Matrix.det_transpose] using hdetT

  -- Unfold `ell` to the determinant of `colsMat`.
  simpa [ell, M] using hdet

end Transport
end Transport
end Hyperlocal
