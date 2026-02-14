/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Correctness.lean

  Route B (Jet-Quotient via σ-sums): Row-0 correctness → Window-3 real stencils.

  This file is pure plumbing/algebra:
  * coefficient facts (realness, nonzero anchor) come from OperatorDefs
  * the only ξ-specific semantic input is the C-only witness:
      `xiJetQuotRow0WitnessC : XiJetQuotRow0WitnessC s`
    (imported from `...Row0Semantics`)
-/

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3

/-- Row-0 deliverable with a nonzero real stencil. -/
structure XiJetQuotRow0Out (s : Hyperlocal.OffSeed Xi) : Type where
  c    : Fin 3 → ℝ
  hc   : c ≠ 0
  hw0  : (toeplitzL 2 (coeffsNat3 c) (w0 s))  (0 : Fin 3) = 0
  hwc  : (toeplitzL 2 (coeffsNat3 c) (wc s))  (0 : Fin 3) = 0
  hwp2 : (toeplitzL 2 (coeffsNat3 c) (wp2 s)) (0 : Fin 3) = 0
  hwp3 : (toeplitzL 2 (coeffsNat3 c) (wp3 s)) (0 : Fin 3) = 0

namespace JetQuotRow0

/-- Real stencil extracted from operator coefficients: `c_i = Re(aRk1_i)`. -/
def cOp (s : Hyperlocal.OffSeed Xi) : Fin 3 → ℝ :=
  fun i => (JetQuotOp.aRk1 s i.1).re

/-- If `z.im = 0` then `z = (z.re : ℂ)`. -/
lemma complex_eq_ofReal_of_im_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

/-- Row-0 agrees when coeffs 0,1,2 are real. -/
lemma toeplitzL_row0_eq_of_real_coeffs
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h0 : (JetQuotOp.aRk1 s 0).im = 0)
    (h1 : (JetQuotOp.aRk1 s 1).im = 0)
    (h2 : (JetQuotOp.aRk1 s 2).im = 0) :
    (toeplitzL 2 (coeffsNat3 (cOp s)) w) (0 : Fin 3)
      = (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) := by
  have hz0 : (coeffsNat3 (cOp s) 0) = JetQuotOp.aRk1 s 0 := by
    have : ((JetQuotOp.aRk1 s 0).re : ℂ) = JetQuotOp.aRk1 s 0 := by
      simpa using (complex_eq_ofReal_of_im_zero (JetQuotOp.aRk1 s 0) h0).symm
    simpa [coeffsNat3_nat0, cOp] using this
  have hz1 : (coeffsNat3 (cOp s) 1) = JetQuotOp.aRk1 s 1 := by
    have : ((JetQuotOp.aRk1 s 1).re : ℂ) = JetQuotOp.aRk1 s 1 := by
      simpa using (complex_eq_ofReal_of_im_zero (JetQuotOp.aRk1 s 1) h1).symm
    simpa [coeffsNat3_nat1, cOp] using this
  have hz2 : (coeffsNat3 (cOp s) 2) = JetQuotOp.aRk1 s 2 := by
    have : ((JetQuotOp.aRk1 s 2).re : ℂ) = JetQuotOp.aRk1 s 2 := by
      simpa using (complex_eq_ofReal_of_im_zero (JetQuotOp.aRk1 s 2) h2).symm
    simpa [coeffsNat3_nat2, cOp] using this
  classical
  simp [toeplitzL_two_apply_fin0, hz0, hz1, hz2,
        add_assoc, add_left_comm, add_comm]

lemma row0_eq_zero_of_op_row0_eq_zero
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h0 : (JetQuotOp.aRk1 s 0).im = 0)
    (h1 : (JetQuotOp.aRk1 s 1).im = 0)
    (h2 : (JetQuotOp.aRk1 s 2).im = 0)
    (hop : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0) :
    (toeplitzL 2 (coeffsNat3 (cOp s)) w) (0 : Fin 3) = 0 := by
  have heq := toeplitzL_row0_eq_of_real_coeffs (s := s) (w := w) h0 h1 h2
  calc
    (toeplitzL 2 (coeffsNat3 (cOp s)) w) (0 : Fin 3)
        = (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) := by simpa using heq
    _ = 0 := hop

/-- Nontriviality: if `aRk1 s j` is real and nonzero, then `cOp s ≠ 0`. -/
lemma cOp_ne_zero_of_aRk1_nonzero_at
    (s : Hyperlocal.OffSeed Xi) (j : Fin 3)
    (hj : (JetQuotOp.aRk1 s j.1).im = 0)
    (haj : JetQuotOp.aRk1 s j.1 ≠ 0) :
    cOp s ≠ 0 := by
  intro hc
  have hcre : cOp s j = 0 := by
    simpa using congrArg (fun f => f j) hc
  have hre : (JetQuotOp.aRk1 s j.1).re = 0 := by
    simpa [cOp] using hcre
  apply haj
  apply Complex.ext <;> simp [hre, hj]

end JetQuotRow0

/-- Build the Row-0 output from the C-only witness + algebraic coefficient facts. -/
noncomputable def xiJetQuotRow0Out (s : Hyperlocal.OffSeed Xi) : XiJetQuotRow0Out s := by
  classical

  -- semantic gate (C-only) — use fully-qualified names to avoid namespace/import ambiguity
  have hC : _root_.Hyperlocal.Targets.XiPacket.XiJetQuotRow0WitnessC s :=
    _root_.Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessC s

  -- (A) realness is pure algebra (from σ-sums in OperatorDefs)
  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  -- (B) nontriviality anchored at j=2 (aRk1 s 2 = -2)
  have ha2 : JetQuotOp.aRk1 s 2 ≠ 0 := JetQuotOp.aRk1_nat2_ne_zero (s := s)

  refine
    { c    := JetQuotRow0.cOp s
      hc   := ?_
      hw0  := ?_
      hwc  := ?_
      hwp2 := ?_
      hwp3 := ?_ }

  · exact JetQuotRow0.cOp_ne_zero_of_aRk1_nonzero_at (s := s) (j := (2 : Fin 3)) hreal2 ha2
  · exact JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero (s := s) (w := w0 s)  hreal0 hreal1 hreal2 hC.hop_w0
  · exact JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wc s)  hreal0 hreal1 hreal2 hC.hop_wc
  · exact JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp2 s) hreal0 hreal1 hreal2 hC.hop_wp2
  · exact JetQuotRow0.row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wp3 s) hreal0 hreal1 hreal2 hC.hop_wp3

/-- Convenience: extracted stencil. -/
def cJet (s : Hyperlocal.OffSeed Xi) : Fin 3 → ℝ :=
  (xiJetQuotRow0Out (s := s)).c

lemma cJet_ne_zero (s : Hyperlocal.OffSeed Xi) : cJet s ≠ 0 :=
  (xiJetQuotRow0Out (s := s)).hc

lemma row0_w0 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (w0 s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hw0

lemma row0_wc (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (wc s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hwc

lemma row0_wp2 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (wp2 s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hwp2

lemma row0_wp3 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (wp3 s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hwp3

theorem xiJetQuotToeplitzL_row0_fromOperator2 (s : Hyperlocal.OffSeed Xi) :
  ∃ c2 : Fin 3 → ℝ,
    c2 ≠ 0 ∧
    (toeplitzL 2 (coeffsNat3 c2) (w0 s))  (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c2) (wc s))  (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c2) (wp2 s)) (0 : Fin 3) = 0 := by
  refine ⟨cJet s, cJet_ne_zero (s := s), ?_, ?_, ?_⟩
  · simpa [cJet] using row0_w0 (s := s)
  · simpa [cJet] using row0_wc (s := s)
  · simpa [cJet] using row0_wp2 (s := s)

theorem xiJetQuotToeplitzL_row0_fromOperator3 (s : Hyperlocal.OffSeed Xi) :
  ∃ c3 : Fin 3 → ℝ,
    c3 ≠ 0 ∧
    (toeplitzL 2 (coeffsNat3 c3) (w0 s))  (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c3) (wc s))  (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c3) (wp3 s)) (0 : Fin 3) = 0 := by
  refine ⟨cJet s, cJet_ne_zero (s := s), ?_, ?_, ?_⟩
  · simpa [cJet] using row0_w0 (s := s)
  · simpa [cJet] using row0_wc (s := s)
  · simpa [cJet] using row0_wp3 (s := s)

end XiPacket
end Targets
end Hyperlocal
