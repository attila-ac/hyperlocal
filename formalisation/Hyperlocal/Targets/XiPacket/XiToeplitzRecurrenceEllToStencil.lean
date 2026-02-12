/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllToStencil.lean

  Pure linear-algebra reverse bridge:

    ell(u0, uc, v) = 0
      ⇒  ∃ c ≠ 0, toeplitzRow3 c u0 ∧ toeplitzRow3 c uc ∧ toeplitzRow3 c v.

  This is the reverse direction of `ell_eq_zero_of_toeplitzRow3` from
  `XiToeplitzRecurrenceExtract.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Field-specialized kernel existence: `det M = 0` ⇒ nontrivial kernel for `mulVec`. -/
private lemma exists_ne_zero_mulVec_eq_zero_of_det_eq_zero
    {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hdet : Matrix.det M = 0) :
    ∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = 0 := by
  classical

  -- `det = 0` ⇒ `det` is not a unit.
  have hnotUnit_det : ¬ IsUnit (Matrix.det M) := by
    simpa [hdet] using (not_isUnit_zero : ¬ IsUnit (0 : ℝ))

  -- `M` not a unit, by `IsUnit M ↔ IsUnit (det M)`.
  have hnotUnit_M : ¬ IsUnit M := by
    intro hUnitM
    exact hnotUnit_det ((Matrix.isUnit_iff_isUnit_det (A := M)).1 hUnitM)

  -- Non-unit ⇒ `mulVec` is not injective (via `mulVec_injective_iff_isUnit`).
  have hnotInj :
      ¬ Function.Injective (fun v : n → ℝ => M.mulVec v) := by
    intro hInj
    have hUnitM : IsUnit M :=
      (Matrix.mulVec_injective_iff_isUnit (A := M)).1 hInj
    exact hnotUnit_M hUnitM

  -- Extract `x,y` with `M*x = M*y` and `x ≠ y` by unfolding injective.
  have h' : ¬ ∀ x y : n → ℝ, M.mulVec x = M.mulVec y → x = y := by
    simpa [Function.Injective] using hnotInj
  rcases not_forall.mp h' with ⟨x, hx⟩
  rcases not_forall.mp hx with ⟨y, hy⟩
  have hImp : M.mulVec x = M.mulVec y ∧ x ≠ y := by
    have h0 : M.mulVec x = M.mulVec y ∧ ¬ x = y := (_root_.not_imp.mp hy)
    refine ⟨h0.1, ?_⟩
    simpa using h0.2

  refine ⟨x - y, sub_ne_zero.mpr hImp.2, ?_⟩

  -- Linearity: `M*(x-y) = M*x - M*y`, then use `M*x = M*y`.
  have hlin : M.mulVec (x - y) = M.mulVec x - M.mulVec y := by
    ext i
    simp [Matrix.mulVec, Finset.sum_sub_distrib, mul_sub]

  simpa [hlin, hImp.1]

/--
`ell(u0, uc, v) = 0` ⇒ there exists a nonzero Toeplitz row stencil `c`
annihilating `u0`, `uc`, `v` (i.e. the three dot-products vanish).
-/
theorem exists_toeplitzRow3_of_ell_eq_zero
    (u0 uc v : Fin 3 → ℝ) (hell : Transport.ell u0 uc v = 0) :
    ∃ c : Fin 3 → ℝ,
      c ≠ 0 ∧ toeplitzRow3 c u0 ∧ toeplitzRow3 c uc ∧ toeplitzRow3 c v := by
  classical
  let M : Matrix (Fin 3) (Fin 3) ℝ := Transport.colsMat u0 uc v

  have hdet : Matrix.det M = 0 := by
    simpa [Transport.ell, M] using hell

  have hdetT : Matrix.det M.transpose = 0 := by
    simpa [Matrix.det_transpose] using hdet

  rcases exists_ne_zero_mulVec_eq_zero_of_det_eq_zero (M := M.transpose) hdetT with
    ⟨c, hc0, hmul⟩

  refine ⟨c, hc0, ?_, ?_, ?_⟩

  · -- u0  (column 0)
    have h0 : (M.transpose.mulVec c) (0 : Fin 3) = 0 := by
      simpa using congrArg (fun f => f (0 : Fin 3)) hmul
    have : (∑ i : Fin 3, u0 i * c i) = 0 := by
      simpa [Matrix.mulVec, M, Transport.colsMat, Transport.baseMat] using h0
    simpa [toeplitzRow3, mul_comm] using this

  · -- uc (column 1)
    have h1 : (M.transpose.mulVec c) (1 : Fin 3) = 0 := by
      simpa using congrArg (fun f => f (1 : Fin 3)) hmul
    have : (∑ i : Fin 3, uc i * c i) = 0 := by
      simpa [Matrix.mulVec, M, Transport.colsMat, Transport.baseMat] using h1
    simpa [toeplitzRow3, mul_comm] using this

  · -- v  (column 2)
    have h2 : (M.transpose.mulVec c) (2 : Fin 3) = 0 := by
      simpa using congrArg (fun f => f (2 : Fin 3)) hmul
    have : (∑ i : Fin 3, v i * c i) = 0 := by
      simpa [Matrix.mulVec, M, Transport.colsMat, Transport.baseMat] using h2
    simpa [toeplitzRow3, mul_comm] using this

end Hyperlocal.Targets.XiPacket
