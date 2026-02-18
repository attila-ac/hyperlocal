/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder.lean

  Semantic bridge (AtOrder): concrete Toeplitz/recurrence output ⇒ ℓ-vanishing
  for the jet-pivot windows at order `m`.

  This is the next “real milestone” for Option-ELL:
  it allows deriving `bCoeff = 0` using κ-nonvanishing witnessed at some
  jet order (from jet-nonflatness), without assuming the legacy value-level
  anchor nonvanishing axiom.

  Current status:
  * This is still a semantic cliff: the actual recurrence-extraction theorem
    for order-`m` jets is not yet formalised.
  * The interface is isolated here so it can later be discharged by a theorem
    without touching downstream algebra.
-/

import Hyperlocal.Transport.Determinant
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Correctness
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3

/-! ### Local helper: `ell = 0` from a nonzero Toeplitz row annihilating three real vectors -/

/--
If a nonzero row stencil `c` annihilates `u0`, `uc`, and `up` (as `toeplitzRow3`),
then the determinant `ell` vanishes.

This is the small linear-algebra bridge used to turn *row-0 Toeplitz constraints*
into the ℓ-vanishings consumed by Option--ELL.
-/
lemma ell_eq_zero_of_toeplitzRow3_local
    (u0 uc up : Fin 3 → ℝ) (c : Fin 3 → ℝ)
    (hc : c ≠ 0)
    (h0 : toeplitzRow3 c u0)
    (hc0 : toeplitzRow3 c uc)
    (hp : toeplitzRow3 c up) :
    Transport.ell u0 uc up = 0 := by
  classical
  refine
    Hyperlocal.Transport.Transport.ell_eq_zero_of_depRow3
      u0 uc up c hc ?_ ?_ ?_
  · simpa [toeplitzRow3] using h0
  · simpa [toeplitzRow3] using hc0
  · simpa [toeplitzRow3] using hp

/--
Route--B “AtOrder” ℓ-output (theorem-level):

From the (AtOrder) row--0 Toeplitz annihilation frontiers for the jet-pivot
windows `w0At m`, `wp2At m`, `wp3At m`, together with the existing row--0
annihilation for `wc` supplied by the Route--B semantic witness
`xiJetQuotRow0WitnessC`, we derive the two determinant vanishings required by
`XiToeplitzEllOutAt m s`.

This discharges the former axiom `xiToeplitzEllOutAt_fromRecurrenceC` and makes
Option--ELL depend only on explicit, isolated row--0 frontiers at order `m`.
-/
theorem xiToeplitzEllOutAt_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOutAt m s := by
  classical

  -- semantic gate for `wc` (C-only witness)
  have hC : _root_.Hyperlocal.Targets.XiPacket.XiJetQuotRow0WitnessC s :=
    _root_.Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessC s

  -- (A) coefficient realness (pure algebra)
  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  -- (B) nontriviality anchored at j=2
  have ha2 : JetQuotOp.aRk1 s 2 ≠ 0 := JetQuotOp.aRk1_nat2_ne_zero (s := s)

  -- choose the real stencil `c := Re(aRk1)`
  let c : Fin 3 → ℝ := JetQuotRow0.cOp s
  have hc : c ≠ 0 :=
    JetQuotRow0.cOp_ne_zero_of_aRk1_nonzero_at (s := s) (j := (2 : Fin 3)) hreal2 ha2

  -- row-0 constraints converted to the real-stencil ToeplitzL form
  have hw0 : (toeplitzL 2 (coeffsNat3 c) (w0At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := w0At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_w0At m s)
  have hwc : (toeplitzL 2 (coeffsNat3 c) (wc s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wc s) hreal0 hreal1 hreal2 hC.hop_wc
  have hwp2 : (toeplitzL 2 (coeffsNat3 c) (wp2At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wp2At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_wp2At m s)
  have hwp3 : (toeplitzL 2 (coeffsNat3 c) (wp3At m s)) (0 : Fin 3) = 0 := by
    exact
      JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero
        (s := s) (w := wp3At m s) hreal0 hreal1 hreal2 (xiJetQuot_row0_wp3At m s)

  -- convert ToeplitzL row-0 constraints into `toeplitzRow3` constraints on real vectors
  have t0 : toeplitzRow3 c (reVec3 (w0At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (w0At m s) hw0
  have tc : toeplitzRow3 c (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wc s) hwc
  have t2 : toeplitzRow3 c (reVec3 (wp2At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wp2At m s) hwp2
  have t3 : toeplitzRow3 c (reVec3 (wp3At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero c (wp3At m s) hwp3

  refine ⟨?_, ?_⟩
  · exact
      ell_eq_zero_of_toeplitzRow3_local
        (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s))
        c hc t0 tc t2
  · exact
      ell_eq_zero_of_toeplitzRow3_local
        (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s))
        c hc t0 tc t3

end XiPacket
end Targets
end Hyperlocal
