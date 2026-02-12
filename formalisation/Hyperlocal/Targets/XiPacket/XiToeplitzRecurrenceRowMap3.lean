/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceRowMap3.lean

  Utility: convert a Window-3 Toeplitz row stencil into a linear functional.
  (Needed by XiToeplitzRecurrenceConcrete.lean’s packaged `XiRecRowPkg` route.)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Standard basis function `e i : Fin 3 → ℝ` (1 at i, 0 elsewhere). -/
private def e (i : Fin 3) : Fin 3 → ℝ := fun j => if j = i then (1 : ℝ) else 0

/--
A row functional induced by coefficients `c : Fin 3 → ℝ`:
`v ↦ ∑ i, c i * v i`.
-/
def rowMap3 (c : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
{ toFun := fun v => (∑ i : Fin 3, c i * v i)
  map_add' := by
    intro v w
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a v
    simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum] }

/-- Evaluation on the standard basis recovers the coefficient. -/
@[simp] lemma rowMap3_apply_e (c : Fin 3 → ℝ) (i : Fin 3) :
    rowMap3 c (e i) = c i := by
  classical
  fin_cases i <;> simp [rowMap3, e, Fin.sum_univ_three]

/-- If `c ≠ 0`, then `rowMap3 c` is a nonzero linear functional. -/
lemma rowMap3_ne_zero_of_coeff_ne_zero (c : Fin 3 → ℝ) (hc : c ≠ 0) :
    rowMap3 c ≠ 0 := by
  classical
  intro hL
  apply hc
  funext i
  have : rowMap3 c (e i) = 0 := by simpa [hL]
  simpa using this.trans (by simp [rowMap3_apply_e])

/-- Convert a Toeplitz-row statement into a linear-functional annihilation. -/
lemma rowMap3_eq_zero_of_toeplitzRow3 (c v : Fin 3 → ℝ) :
    toeplitzRow3 c v → rowMap3 c v = 0 := by
  intro h
  simpa [toeplitzRow3, rowMap3] using h

end Hyperlocal.Targets.XiPacket
