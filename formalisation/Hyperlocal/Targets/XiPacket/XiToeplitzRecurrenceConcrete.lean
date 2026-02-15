/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceConcrete.lean

  Concrete ξ jet-quotient recurrence extraction layer ⇒ Window-3 row stencils.

  Immediate goal:
  eliminate the dependency on the JetQuotient Row0-axiom
    `axiom xiJetQuot_row0_witnessC`
  by taking the *concrete extraction output* as the interface:
    • a nonzero row stencil for p=2 annihilating (w0,wc,wp2) in the real lane
    • a nonzero row stencil for p=3 annihilating (w0,wc,wp3) in the real lane

  Downstream plumbing remains unchanged:
  we package these as a nonzero linear functional `XiRecRow s p` on (Fin 3 → ℝ),
  and expose the annihilation facts needed by the manufacturing layer.

  NOTE:
  This file is intentionally *real-lane* (row stencils / linear functionals).
  It does NOT build a complex Toeplitz operator, and it does NOT use any
  `toeplitzRow3_iff` lemma (that one lives in the manufacturing layer file).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Correctness
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceRowMap3
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3

/--
Concrete recurrence extraction for p=2: produces a nonzero Window-3 Toeplitz row stencil
annihilating `reVec3(w0)`, `reVec3(wc)`, and `reVec3(wp2)`.

(Derived from the jet-quotient operator correctness layer.)
-/
theorem xiRecStencil2 (s : Hyperlocal.OffSeed Xi) :
  ∃ c2 : Fin 3 → ℝ,
    c2 ≠ 0 ∧
    toeplitzRow3 c2 (reVec3 (w0 s)) ∧
    toeplitzRow3 c2 (reVec3 (wc s)) ∧
    toeplitzRow3 c2 (reVec3 (wp2 s)) := by
  rcases xiJetQuotToeplitzL_row0_fromOperator2 (s := s) with
    ⟨c2, hc2, hw0, hwc, hwp2⟩
  refine ⟨c2, hc2, ?_, ?_, ?_⟩
  · exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c2 (w0 s) hw0
  · exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c2 (wc s) hwc
  · exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c2 (wp2 s) hwp2

/--
Concrete recurrence extraction for p=3: produces a nonzero Window-3 Toeplitz row stencil
annihilating `reVec3(w0)`, `reVec3(wc)`, and `reVec3(wp3)`.

(Derived from the jet-quotient operator correctness layer.)
-/
theorem xiRecStencil3 (s : Hyperlocal.OffSeed Xi) :
  ∃ c3 : Fin 3 → ℝ,
    c3 ≠ 0 ∧
    toeplitzRow3 c3 (reVec3 (w0 s)) ∧
    toeplitzRow3 c3 (reVec3 (wc s)) ∧
    toeplitzRow3 c3 (reVec3 (wp3 s)) := by
  rcases xiJetQuotToeplitzL_row0_fromOperator3 (s := s) with
    ⟨c3, hc3, hw0, hwc, hwp3⟩
  refine ⟨c3, hc3, ?_, ?_, ?_⟩
  · exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c3 (w0 s) hw0
  · exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c3 (wc s) hwc
  · exact toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c3 (wp3 s) hwp3

/--
Packaged concrete recurrence output for ξ at Window-3:

`L2, L3` are the *row functionals* (linear maps) induced by the extracted stencils,
and the `h*_*` fields are the annihilation facts on the three definitional windows.
-/
structure XiRecRowPkg (s : Hyperlocal.OffSeed Xi) : Type where
  L2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ
  L3 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ
  h2_nonzero : L2 ≠ 0
  h3_nonzero : L3 ≠ 0
  h2_w0 : L2 (reVec3 (w0 s)) = 0
  h2_wc : L2 (reVec3 (wc s)) = 0
  h2_wp2 : L2 (reVec3 (wp2 s)) = 0
  h3_w0 : L3 (reVec3 (w0 s)) = 0
  h3_wc : L3 (reVec3 (wc s)) = 0
  h3_wp3 : L3 (reVec3 (wp3 s)) = 0

/-- Build the packaged recurrence rows from the concrete stencil theorems. -/
noncomputable def xiRecRowPkg (s : Hyperlocal.OffSeed Xi) : XiRecRowPkg s := by
  classical
  -- choose the stencils
  let c2 : Fin 3 → ℝ := Classical.choose (xiRecStencil2 s)
  let c3 : Fin 3 → ℝ := Classical.choose (xiRecStencil3 s)

  have hc2 : c2 ≠ 0 := (Classical.choose_spec (xiRecStencil2 s)).1
  have hc3 : c3 ≠ 0 := (Classical.choose_spec (xiRecStencil3 s)).1

  -- unpack row annihilations
  have h2_w0' : toeplitzRow3 c2 (reVec3 (w0 s)) := (Classical.choose_spec (xiRecStencil2 s)).2.1
  have h2_wc' : toeplitzRow3 c2 (reVec3 (wc s)) := (Classical.choose_spec (xiRecStencil2 s)).2.2.1
  have h2_wp2' : toeplitzRow3 c2 (reVec3 (wp2 s)) := (Classical.choose_spec (xiRecStencil2 s)).2.2.2

  have h3_w0' : toeplitzRow3 c3 (reVec3 (w0 s)) := (Classical.choose_spec (xiRecStencil3 s)).2.1
  have h3_wc' : toeplitzRow3 c3 (reVec3 (wc s)) := (Classical.choose_spec (xiRecStencil3 s)).2.2.1
  have h3_wp3' : toeplitzRow3 c3 (reVec3 (wp3 s)) := (Classical.choose_spec (xiRecStencil3 s)).2.2.2

  refine
    ⟨rowMap3 c2, rowMap3 c3,
      ?_, ?_,
      ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · exact rowMap3_ne_zero_of_coeff_ne_zero (c := c2) hc2
  · exact rowMap3_ne_zero_of_coeff_ne_zero (c := c3) hc3
  · exact rowMap3_eq_zero_of_toeplitzRow3 (c := c2) (v := reVec3 (w0 s)) h2_w0'
  · exact rowMap3_eq_zero_of_toeplitzRow3 (c := c2) (v := reVec3 (wc s)) h2_wc'
  · exact rowMap3_eq_zero_of_toeplitzRow3 (c := c2) (v := reVec3 (wp2 s)) h2_wp2'
  · exact rowMap3_eq_zero_of_toeplitzRow3 (c := c3) (v := reVec3 (w0 s)) h3_w0'
  · exact rowMap3_eq_zero_of_toeplitzRow3 (c := c3) (v := reVec3 (wc s)) h3_wc'
  · exact rowMap3_eq_zero_of_toeplitzRow3 (c := c3) (v := reVec3 (wp3 s)) h3_wp3'

/-- The concrete recurrence row functional for ξ, parameterized by `p`. -/
noncomputable def XiRecRow (s : Hyperlocal.OffSeed Xi) (p : ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  let pkg := xiRecRowPkg s
  if h : p = 2 then pkg.L2 else pkg.L3

theorem XiRecRow_two (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) = (xiRecRowPkg s).L2 := by
  classical
  simp [XiRecRow]

theorem XiRecRow_three (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) = (xiRecRowPkg s).L3 := by
  classical
  have h : (3 : ℝ) ≠ 2 := by norm_num
  simp [XiRecRow, h]

theorem XiRecRow_ne_zero_2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) ≠ 0 := by
  classical
  simpa [XiRecRow_two] using (xiRecRowPkg s).h2_nonzero

theorem XiRecRow_ne_zero_3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) ≠ 0 := by
  classical
  simpa [XiRecRow_three] using (xiRecRowPkg s).h3_nonzero

theorem XiRecRow_w0_2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) (reVec3 (w0 s)) = 0 := by
  classical
  simpa [XiRecRow_two] using (xiRecRowPkg s).h2_w0

theorem XiRecRow_wc_2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) (reVec3 (wc s)) = 0 := by
  classical
  simpa [XiRecRow_two] using (xiRecRowPkg s).h2_wc

theorem XiRecRow_wp2 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (2 : ℝ) (reVec3 (wp2 s)) = 0 := by
  classical
  simpa [XiRecRow_two] using (xiRecRowPkg s).h2_wp2

theorem XiRecRow_w0_3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) (reVec3 (w0 s)) = 0 := by
  classical
  simpa [XiRecRow_three] using (xiRecRowPkg s).h3_w0

theorem XiRecRow_wc_3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) (reVec3 (wc s)) = 0 := by
  classical
  simpa [XiRecRow_three] using (xiRecRowPkg s).h3_wc

theorem XiRecRow_wp3 (s : Hyperlocal.OffSeed Xi) :
    XiRecRow s (3 : ℝ) (reVec3 (wp3 s)) = 0 := by
  classical
  simpa [XiRecRow_three] using (xiRecRowPkg s).h3_wp3

end XiPacket
end Targets
end Hyperlocal
