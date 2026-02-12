/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceConcrete.lean

  Concrete recurrence-row interface (Window 3, Re-lane).

  Goal (next semantic work):
  replace the single axiom `xiJetQuotRecOut` (in `XiToeplitzRecurrenceJetQuotient.lean`)
  by an actual construction extracted from the jet-quotient recurrence operator.
  This file then packages those stencils as linear row functionals `L2/L3`.

  For now, this file:
  • bundles the p=2 and p=3 row functionals + specs into ONE package structure
  • defines `xiRecRowPkg` by converting the stencil output `c2/c3` into linear maps
    via `rowMap3`
  • defines `XiRecRow s p` by selecting `L2/L3` (otherwise 0)
  • exposes the old names `XiRecRow_*` as theorems (projection lemmas)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotient
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/--
Jet-quotient recurrence output at Window 3 in the real lane:

two nonzero row functionals (for p=2 and p=3) annihilating the three relevant
real-window vectors `reVec3(w0)`, `reVec3(wc)`, and `reVec3(wp2/wp3)`.
-/
structure XiRecRowPkg (s : Hyperlocal.OffSeed Xi) : Type where
  L2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ
  L3 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ
  hL2_ne : L2 ≠ 0
  hL3_ne : L3 ≠ 0
  hw0_2 : L2 (reVec3 (w0 s)) = 0
  hwc_2 : L2 (reVec3 (wc s)) = 0
  hwp2  : L2 (reVec3 (wp2 s)) = 0
  hw0_3 : L3 (reVec3 (w0 s)) = 0
  hwc_3 : L3 (reVec3 (wc s)) = 0
  hwp3  : L3 (reVec3 (wp3 s)) = 0

/--
Concrete package extracted from the (current) jet-quotient recurrence output.

Semantic cliff (next task): implement `xiJetQuotRecOut` from the actual
jet-quotient recurrence operator.

Once `xiJetQuotRecOut` is theorem-level, this package becomes theorem-level
without changing any downstream consumers.
-/
noncomputable def xiRecRowPkg (s : Hyperlocal.OffSeed Xi) : XiRecRowPkg s := by
  classical
  refine
    { L2 := rowMap3 (xiJetQuotRecOut s).c2
      L3 := rowMap3 (xiJetQuotRecOut s).c3
      hL2_ne :=
        rowMap3_ne_zero_of_coeff_ne_zero
          (c := (xiJetQuotRecOut s).c2) (xiJetQuotRecOut s).hc2_ne
      hL3_ne :=
        rowMap3_ne_zero_of_coeff_ne_zero
          (c := (xiJetQuotRecOut s).c3) (xiJetQuotRecOut s).hc3_ne
      hw0_2 := by
        exact rowMap3_eq_zero_of_toeplitzRow3
          (c := (xiJetQuotRecOut s).c2) (v := reVec3 (w0 s))
          (xiJetQuotRecOut s).hw0_2
      hwc_2 := by
        exact rowMap3_eq_zero_of_toeplitzRow3
          (c := (xiJetQuotRecOut s).c2) (v := reVec3 (wc s))
          (xiJetQuotRecOut s).hwc_2
      hwp2 := by
        exact rowMap3_eq_zero_of_toeplitzRow3
          (c := (xiJetQuotRecOut s).c2) (v := reVec3 (wp2 s))
          (xiJetQuotRecOut s).hwp2
      hw0_3 := by
        exact rowMap3_eq_zero_of_toeplitzRow3
          (c := (xiJetQuotRecOut s).c3) (v := reVec3 (w0 s))
          (xiJetQuotRecOut s).hw0_3
      hwc_3 := by
        exact rowMap3_eq_zero_of_toeplitzRow3
          (c := (xiJetQuotRecOut s).c3) (v := reVec3 (wc s))
          (xiJetQuotRecOut s).hwc_3
      hwp3 := by
        exact rowMap3_eq_zero_of_toeplitzRow3
          (c := (xiJetQuotRecOut s).c3) (v := reVec3 (wp3 s))
          (xiJetQuotRecOut s).hwp3 }

/--
Concrete recurrence row functional for a given prime `p`.

For this project we only consume `p=2` and `p=3`; for other `p` return `0`.
-/
noncomputable def XiRecRow (s : Hyperlocal.OffSeed Xi) (p : ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  if hp2 : p = (2 : ℝ) then (xiRecRowPkg s).L2
  else if hp3 : p = (3 : ℝ) then (xiRecRowPkg s).L3
  else 0

@[simp] lemma XiRecRow_two (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) = (xiRecRowPkg s).L2 := by
  simp [XiRecRow]

@[simp] lemma XiRecRow_three (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) = (xiRecRowPkg s).L3 := by
  have h : (3 : ℝ) ≠ (2 : ℝ) := by norm_num
  simp [XiRecRow, h]

/-- Nontriviality for the two primes we use. -/
theorem XiRecRow_ne_zero_2 (s : Hyperlocal.OffSeed Xi) : XiRecRow s (2 : ℝ) ≠ 0 := by
  simpa using (xiRecRowPkg s).hL2_ne

theorem XiRecRow_ne_zero_3 (s : Hyperlocal.OffSeed Xi) : XiRecRow s (3 : ℝ) ≠ 0 := by
  simpa using (xiRecRowPkg s).hL3_ne

/-- Window annihilations for p=2. -/
theorem XiRecRow_w0_2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) (reVec3 (w0 s)) = 0 := by
  simpa using (xiRecRowPkg s).hw0_2

theorem XiRecRow_wc_2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) (reVec3 (wc s)) = 0 := by
  simpa using (xiRecRowPkg s).hwc_2

theorem XiRecRow_wp2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) (reVec3 (wp2 s)) = 0 := by
  simpa using (xiRecRowPkg s).hwp2

/-- Window annihilations for p=3. -/
theorem XiRecRow_w0_3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) (reVec3 (w0 s)) = 0 := by
  simpa using (xiRecRowPkg s).hw0_3

theorem XiRecRow_wc_3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) (reVec3 (wc s)) = 0 := by
  simpa using (xiRecRowPkg s).hwc_3

theorem XiRecRow_wp3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) (reVec3 (wp3 s)) = 0 := by
  simpa using (xiRecRowPkg s).hwp3

end Hyperlocal.Targets.XiPacket
