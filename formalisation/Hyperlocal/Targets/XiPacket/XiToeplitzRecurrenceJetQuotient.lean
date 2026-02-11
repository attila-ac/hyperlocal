/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotient.lean

  First draft (builds, “yellow-ready”): jet-quotient recurrence operator → Window-3 row stencils.

  Purpose:
  This is the *next semantic layer* under `XiToeplitzRecurrenceConcrete.lean`.

  • Here we introduce an abstract “jet-quotient recurrence output” consisting of
    two Window-3 Toeplitz row stencils (for p=2 and p=3) in the Re-lane.
  • We then derive:
      (1) the Window annihilations in *linear-functional* form, and
      (2) `XiMinimalModelRecurrenceHyp s` (finite-window extraction form).

  TODO (next step):
  Replace the single axiom `xiJetQuotRecOut` below by an actual construction
  from your jet-quotient recurrence operator (Cauchy-product / Toeplitz machinery).

  Hook plan:
  Once `xiJetQuotRecOut` is theorem-level, you can either:
  (A) prove `XiMinimalModelRecurrenceHyp s` directly (this file already does), or
  (B) rebuild your packaged `XiRecRowPkg s` (L2/L3) by converting these stencils
      into linear maps `rowMap3 c2`, `rowMap3 c3`.
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
    -- rewrite RHS `a * (∑ ...)` into a sum and normalize
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
  -- evaluate the (supposedly) zero functional on the basis vector `e i`
  have : rowMap3 c (e i) = 0 := by simpa [hL]
  simpa using this.trans (by simp [rowMap3_apply_e])

/-- Convert a Toeplitz-row statement into a linear-functional annihilation. -/
lemma rowMap3_eq_zero_of_toeplitzRow3 (c v : Fin 3 → ℝ) :
    toeplitzRow3 c v → rowMap3 c v = 0 := by
  intro h
  simpa [toeplitzRow3, rowMap3] using h

/--
Abstract jet-quotient recurrence output at Window 3 in the real lane.

This is the *semantic target* of your upcoming concrete implementation.
-/
structure XiJetQuotRecOut (s : Hyperlocal.OffSeed Xi) : Type where
  c2 : Fin 3 → ℝ
  c3 : Fin 3 → ℝ
  hc2_ne : c2 ≠ 0
  hc3_ne : c3 ≠ 0
  hw0_2 : toeplitzRow3 c2 (reVec3 (w0 s))
  hwc_2 : toeplitzRow3 c2 (reVec3 (wc s))
  hwp2  : toeplitzRow3 c2 (reVec3 (wp2 s))
  hw0_3 : toeplitzRow3 c3 (reVec3 (w0 s))
  hwc_3 : toeplitzRow3 c3 (reVec3 (wc s))
  hwp3  : toeplitzRow3 c3 (reVec3 (wp3 s))

/--
**Single semantic cliff (next task):**
replace this axiom by an actual definition extracted from the jet-quotient recurrence operator.
-/
axiom xiJetQuotRecOut (s : Hyperlocal.OffSeed Xi) : XiJetQuotRecOut s

/--
Jet-quotient recurrence row functional at prime `p`.

For now we only expose `p=2,3`; other `p` map to `0`.
-/
noncomputable def XiJetQuotRecRow (s : Hyperlocal.OffSeed Xi) (p : ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  if hp2 : p = (2 : ℝ) then rowMap3 (xiJetQuotRecOut s).c2
  else if hp3 : p = (3 : ℝ) then rowMap3 (xiJetQuotRecOut s).c3
  else 0

@[simp] lemma XiJetQuotRecRow_two (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (2 : ℝ) = rowMap3 (xiJetQuotRecOut s).c2 := by
  simp [XiJetQuotRecRow]

@[simp] lemma XiJetQuotRecRow_three (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (3 : ℝ) = rowMap3 (xiJetQuotRecOut s).c3 := by
  have h : (3 : ℝ) ≠ (2 : ℝ) := by norm_num
  simp [XiJetQuotRecRow, h]

/-- Nontriviality for p=2. -/
theorem XiJetQuotRecRow_ne_zero_2 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (2 : ℝ) ≠ 0 := by
  simpa [XiJetQuotRecRow_two] using
    (rowMap3_ne_zero_of_coeff_ne_zero (c := (xiJetQuotRecOut s).c2) (xiJetQuotRecOut s).hc2_ne)

/-- Nontriviality for p=3. -/
theorem XiJetQuotRecRow_ne_zero_3 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (3 : ℝ) ≠ 0 := by
  simpa [XiJetQuotRecRow_three] using
    (rowMap3_ne_zero_of_coeff_ne_zero (c := (xiJetQuotRecOut s).c3) (xiJetQuotRecOut s).hc3_ne)

/-- Window annihilations for p=2 (linear-functional form). -/
theorem XiJetQuotRecRow_w0_2 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (2 : ℝ) (reVec3 (w0 s)) = 0 := by
  have h := (xiJetQuotRecOut s).hw0_2
  simpa [XiJetQuotRecRow_two] using
    (rowMap3_eq_zero_of_toeplitzRow3 (c := (xiJetQuotRecOut s).c2) (v := reVec3 (w0 s)) h)

theorem XiJetQuotRecRow_wc_2 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (2 : ℝ) (reVec3 (wc s)) = 0 := by
  have h := (xiJetQuotRecOut s).hwc_2
  simpa [XiJetQuotRecRow_two] using
    (rowMap3_eq_zero_of_toeplitzRow3 (c := (xiJetQuotRecOut s).c2) (v := reVec3 (wc s)) h)

theorem XiJetQuotRecRow_wp2 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (2 : ℝ) (reVec3 (wp2 s)) = 0 := by
  have h := (xiJetQuotRecOut s).hwp2
  simpa [XiJetQuotRecRow_two] using
    (rowMap3_eq_zero_of_toeplitzRow3 (c := (xiJetQuotRecOut s).c2) (v := reVec3 (wp2 s)) h)

/-- Window annihilations for p=3 (linear-functional form). -/
theorem XiJetQuotRecRow_w0_3 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (3 : ℝ) (reVec3 (w0 s)) = 0 := by
  have h := (xiJetQuotRecOut s).hw0_3
  simpa [XiJetQuotRecRow_three] using
    (rowMap3_eq_zero_of_toeplitzRow3 (c := (xiJetQuotRecOut s).c3) (v := reVec3 (w0 s)) h)

theorem XiJetQuotRecRow_wc_3 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (3 : ℝ) (reVec3 (wc s)) = 0 := by
  have h := (xiJetQuotRecOut s).hwc_3
  simpa [XiJetQuotRecRow_three] using
    (rowMap3_eq_zero_of_toeplitzRow3 (c := (xiJetQuotRecOut s).c3) (v := reVec3 (wc s)) h)

theorem XiJetQuotRecRow_wp3 (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRecRow s (3 : ℝ) (reVec3 (wp3 s)) = 0 := by
  have h := (xiJetQuotRecOut s).hwp3
  simpa [XiJetQuotRecRow_three] using
    (rowMap3_eq_zero_of_toeplitzRow3 (c := (xiJetQuotRecOut s).c3) (v := reVec3 (wp3 s)) h)

/--
**Direct bridge to your finite-window hypothesis:**
jet-quotient recurrence output ⇒ `XiMinimalModelRecurrenceHyp s`.
-/
theorem xiMinimalModelRecurrenceHyp_fromJetQuot (s : Hyperlocal.OffSeed Xi) :
    XiMinimalModelRecurrenceHyp s := by
  refine ⟨?h2, ?h3⟩
  · refine ⟨(xiJetQuotRecOut s).c2, (xiJetQuotRecOut s).hc2_ne,
      (xiJetQuotRecOut s).hw0_2, (xiJetQuotRecOut s).hwc_2, (xiJetQuotRecOut s).hwp2⟩
  · refine ⟨(xiJetQuotRecOut s).c3, (xiJetQuotRecOut s).hc3_ne,
      (xiJetQuotRecOut s).hw0_3, (xiJetQuotRecOut s).hwc_3, (xiJetQuotRecOut s).hwp3⟩

end Hyperlocal.Targets.XiPacket
