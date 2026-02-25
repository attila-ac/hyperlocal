/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ManuscriptFromSigmaAndRow012.lean

  Build the manuscript-facing 9-lemma tail instance from *coordinate* facts
  (sigma + Row012 stencil + σ3≠0), not from convCoeff directly.

  Assumptions:
    [XiAtOrderSigmaProvider]                      -- gives row0Sigma=0 for canonical windows
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]  -- gives Row012ConvolutionAtRev for canonical windows
    [XiSigma3Nonzero]                             -- σ3(s) ≠ 0 (strip branch should prove this)

  Output:
    instance : XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Reductions
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ShiftCoord

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic   -- class XiRow012ConvolutionAtRevAtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiSigma3Nonzero

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

namespace Tail345ManuscriptFromSigmaAndRow012

/-- From (-σ3)*x = 0 and σ3 ≠ 0, deduce x = 0. -/
private lemma eq_zero_of_neg_sigma3_mul_eq_zero
    (s : OffSeed Xi) (x : ℂ)
    (hσ3 : (JetQuotOp.σ3 s : ℂ) ≠ 0)
    (h : (-(JetQuotOp.σ3 s : ℂ)) * x = 0) : x = 0 := by
  have hneg : (-(JetQuotOp.σ3 s : ℂ)) ≠ 0 := neg_ne_zero.mpr hσ3
  have hx : (-(JetQuotOp.σ3 s : ℂ)) = 0 ∨ x = 0 := mul_eq_zero.mp h
  cases hx with
  | inl hbad => exact False.elim (hneg hbad)
  | inr hx0  => exact hx0

/--
Core coordinate kill lemma:

Given:
  row0Sigma s w = 0
  Row012ConvolutionAtRev s z w
  σ3(s) ≠ 0

Deduce: w0=w1=w2=0.
-/
theorem coords012_eq_zero_of_sigma_and_row012
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (hSigma : row0Sigma s w = 0)
    (H : Row012ConvolutionAtRev s z w)
    (hσ3 : (JetQuotOp.σ3 s : ℂ) ≠ 0) :
    (w 0) = 0 ∧ (w 1) = 0 ∧ (w 2) = 0 := by
  have hsh1 :
      (JetQuotOp.σ2 s) * (w 2) + (-JetQuotOp.σ3 s) * (w 1) = 0 :=
    Tail345ShiftCoord.sigma_shift1_coord_eq_zero_of_row012ConvolutionAtRev
      (s := s) (z := z) (w := w) H

  have hsh2 : (-JetQuotOp.σ3 s) * (w 2) = 0 :=
    Tail345ShiftCoord.sigma_shift2_coord_eq_zero_of_row012ConvolutionAtRev
      (s := s) (z := z) (w := w) H

  have hw2 : (w 2) = 0 :=
    eq_zero_of_neg_sigma3_mul_eq_zero (s := s) (x := (w 2)) hσ3 (by simpa using hsh2)

  have hmul1 : (-(JetQuotOp.σ3 s : ℂ)) * (w 1) = 0 := by
    simpa [hw2, add_zero] using hsh1

  have hw1 : (w 1) = 0 :=
    eq_zero_of_neg_sigma3_mul_eq_zero (s := s) (x := (w 1)) hσ3 hmul1

  have hmul0 : (-(JetQuotOp.σ3 s : ℂ)) * (w 0) = 0 := by
    have : (-(JetQuotOp.σ3 s : ℂ)) * (w 0) = row0Sigma s w := by
      simp [row0Sigma, hw1, hw2, add_assoc, add_left_comm, add_comm]
    calc
      (-(JetQuotOp.σ3 s : ℂ)) * (w 0) = row0Sigma s w := this
      _ = 0 := hSigma

  have hw0 : (w 0) = 0 :=
    eq_zero_of_neg_sigma3_mul_eq_zero (s := s) (x := (w 0)) hσ3 hmul0

  exact ⟨hw0, hw1, hw2⟩

/--
For a single window `w`, sigma + row012 + σ3≠0 implies the three tail vanishings at n=3,4,5.
-/
theorem tail345_for_window_of_sigma_and_row012
    [XiSigma3Nonzero]
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (hSigma : row0Sigma s w = 0)
    (H : Row012ConvolutionAtRev s z w) :
    (Cancellation.convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0) ∧
    (Cancellation.convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0) ∧
    (Cancellation.convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0) := by
  have hσ3 : (JetQuotOp.σ3 s : ℂ) ≠ 0 := XiSigma3Nonzero.sigma3_ne_zero (s := s)

  have hcoords :=
    coords012_eq_zero_of_sigma_and_row012
      (s := s) (z := z) (w := w) (hSigma := hSigma) (H := H) (hσ3 := hσ3)

  have hw0 : w 0 = 0 := hcoords.1
  have hw1 : w 1 = 0 := hcoords.2.1

  have ht3 : Cancellation.convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 :=
    (Tail345Reductions.tail3_iff_row0Sigma (s := s) (w := w)).2 hSigma

  have ht5 : Cancellation.convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 :=
    (Tail345Reductions.tail5_iff_w0 (s := s) (w := w)).2 hw0

  have hB4 : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 := by
    simp [hw0, hw1]

  have ht4 : Cancellation.convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 :=
    (Tail345Reductions.tail4_iff_lincomb (s := s) (w := w)).2 hB4

  exact ⟨ht3, ht4, ht5⟩

/--
Main result: global manuscript 9-lemma instance from global sigma + global Row012 + σ3≠0.
-/
instance (priority := 900)
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro m s
    have hSigma : row0Sigma s (w0At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hw0AtSigma
    have H : Row012ConvolutionAtRev s s.ρ (w0At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012 (s := s) (z := s.ρ) (w := w0At m s) hSigma H).1

  · intro m s
    have hSigma : row0Sigma s (w0At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hw0AtSigma
    have H : Row012ConvolutionAtRev s s.ρ (w0At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012 (s := s) (z := s.ρ) (w := w0At m s) hSigma H).2.1

  · intro m s
    have hSigma : row0Sigma s (w0At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hw0AtSigma
    have H : Row012ConvolutionAtRev s s.ρ (w0At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012 (s := s) (z := s.ρ) (w := w0At m s) hSigma H).2.2

  · intro m s
    have hSigma : row0Sigma s (wp2At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp2AtSigma
    have H : Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) hSigma H).1

  · intro m s
    have hSigma : row0Sigma s (wp2At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp2AtSigma
    have H : Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) hSigma H).2.1

  · intro m s
    have hSigma : row0Sigma s (wp2At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp2AtSigma
    have H : Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) hSigma H).2.2

  · intro m s
    have hSigma : row0Sigma s (wp3At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp3AtSigma
    have H : Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp3At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) hSigma H).1

  · intro m s
    have hSigma : row0Sigma s (wp3At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp3AtSigma
    have H : Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp3At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) hSigma H).2.1

  · intro m s
    have hSigma : row0Sigma s (wp3At m s) = 0 :=
      (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp3AtSigma
    have H : Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp3At (m := m) (s := s)
    exact (tail345_for_window_of_sigma_and_row012
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) hSigma H).2.2

end Tail345ManuscriptFromSigmaAndRow012

end XiPacket
end Targets
end Hyperlocal
