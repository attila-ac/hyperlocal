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
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceRowMap3
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

noncomputable def xiRecRowPkg (s : Hyperlocal.OffSeed Xi) : XiRecRowPkg s := by
  classical

  -- existence proofs (Prop)
  have h2 :
      ∃ c2 : Fin 3 → ℝ,
        c2 ≠ 0 ∧
        toeplitzRow3 c2 (reVec3 (w0 s)) ∧
        toeplitzRow3 c2 (reVec3 (wc s)) ∧
        toeplitzRow3 c2 (reVec3 (wp2 s)) :=
    xiJetQuotStencil_spec2 s

  have h3 :
      ∃ c3 : Fin 3 → ℝ,
        c3 ≠ 0 ∧
        toeplitzRow3 c3 (reVec3 (w0 s)) ∧
        toeplitzRow3 c3 (reVec3 (wc s)) ∧
        toeplitzRow3 c3 (reVec3 (wp3 s)) :=
    xiJetQuotStencil_spec3 s

  -- choose witnesses (now in data, not Prop-elim)
  let c2 : Fin 3 → ℝ := Classical.choose h2
  have hc2 :
      c2 ≠ 0 ∧
      toeplitzRow3 c2 (reVec3 (w0 s)) ∧
      toeplitzRow3 c2 (reVec3 (wc s)) ∧
      toeplitzRow3 c2 (reVec3 (wp2 s)) :=
    Classical.choose_spec h2

  let c3 : Fin 3 → ℝ := Classical.choose h3
  have hc3 :
      c3 ≠ 0 ∧
      toeplitzRow3 c3 (reVec3 (w0 s)) ∧
      toeplitzRow3 c3 (reVec3 (wc s)) ∧
      toeplitzRow3 c3 (reVec3 (wp3 s)) :=
    Classical.choose_spec h3

  -- unpack the conjunctions (Prop → Prop, allowed)
  have hc2_ne : c2 ≠ 0 := hc2.1
  have hw0_2  : toeplitzRow3 c2 (reVec3 (w0 s)) := hc2.2.1
  have hwc_2  : toeplitzRow3 c2 (reVec3 (wc s)) := hc2.2.2.1
  have hwp2   : toeplitzRow3 c2 (reVec3 (wp2 s)) := hc2.2.2.2

  have hc3_ne : c3 ≠ 0 := hc3.1
  have hw0_3  : toeplitzRow3 c3 (reVec3 (w0 s)) := hc3.2.1
  have hwc_3  : toeplitzRow3 c3 (reVec3 (wc s)) := hc3.2.2.1
  have hwp3   : toeplitzRow3 c3 (reVec3 (wp3 s)) := hc3.2.2.2

  -- build the package
  refine
    { L2 := rowMap3 c2
      L3 := rowMap3 c3
      hL2_ne := rowMap3_ne_zero_of_coeff_ne_zero (c := c2) hc2_ne
      hL3_ne := rowMap3_ne_zero_of_coeff_ne_zero (c := c3) hc3_ne
      hw0_2 := rowMap3_eq_zero_of_toeplitzRow3 (c := c2) (v := reVec3 (w0 s)) hw0_2
      hwc_2 := rowMap3_eq_zero_of_toeplitzRow3 (c := c2) (v := reVec3 (wc s)) hwc_2
      hwp2  := rowMap3_eq_zero_of_toeplitzRow3 (c := c2) (v := reVec3 (wp2 s)) hwp2
      hw0_3 := rowMap3_eq_zero_of_toeplitzRow3 (c := c3) (v := reVec3 (w0 s)) hw0_3
      hwc_3 := rowMap3_eq_zero_of_toeplitzRow3 (c := c3) (v := reVec3 (wc s)) hwc_3
      hwp3  := rowMap3_eq_zero_of_toeplitzRow3 (c := c3) (v := reVec3 (wp3 s)) hwp3 }

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
