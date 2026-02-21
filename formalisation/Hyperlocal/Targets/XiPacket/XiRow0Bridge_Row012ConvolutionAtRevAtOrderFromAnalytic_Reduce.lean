/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce.lean

  Cycle-safe reduction of the remaining admitted boundary.

  We already have, for each AtOrder window, a proof of:
    Row0ConvolutionAtRev s z w
  from the Route–B analytic witness (Toeplitz → row0Sigma → convCoeff n=3).

  To upgrade to Row012ConvolutionAtRev (n=3,4,5), it suffices to prove the
  two additional linear constraints corresponding to convCoeff n=4 and n=5.

  This file avoids relying on lemma names in Row0Coeff345Algebra by
  proving the n=4/n=5 closed forms locally (pure algebra, cycle-safe).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateFromAnalytic
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- The two extra linear constraints that correspond to reverse convCoeff 4 and 5. -/
structure Row012ExtraLin (s : OffSeed Xi) (w : Window 3) : Prop where
  h4 : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0
  h5 : (-2 : ℂ) * (w 0) = 0

/-- Closed form for the n=4 reverse Cauchy coefficient (local, algebra-only). -/
theorem convCoeff_rev_eq_n4
    (s : OffSeed Xi) (w : Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4
      = (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) := by
  classical
  -- Expand; then normalize the ring expression so term order doesn't matter.
  simp [convCoeff, row0CoeffSeqRev, winSeqRev, Finset.range_succ]
  ring_nf

/-- Closed form for the n=5 reverse Cauchy coefficient (local, algebra-only). -/
theorem convCoeff_rev_eq_n5
    (s : OffSeed Xi) (w : Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5
      = (-2 : ℂ) * (w 0) := by
  classical
  simp [convCoeff, row0CoeffSeqRev, winSeqRev, Finset.range_succ]

/--
Upgrade: Row0ConvolutionAtRev + the two extra linear constraints
⇒ Row012ConvolutionAtRev.
-/
theorem row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
    (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H0 : Row0ConvolutionAtRev s z w)
    (HL : Row012ExtraLin s w) :
    Row012ConvolutionAtRev s z w := by
  classical
  rcases H0 with ⟨G, hfac, hjet, h3⟩

  have h4coeff : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := w)]
    simpa using HL.h4

  have h5coeff : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := w)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4coeff, h5coeff⟩

/-!
  Now specialize the reduction to the three AtOrder windows using the existing
  Row0ConvolutionAtRev-from-analytic theorems.
-/

/-- Reduction target: Row012 stencil at w0At from analytic + two linear constraints. -/
theorem row012ConvolutionAtRev_w0At_fromAnalytic_of_extraLin
    (m : ℕ) (s : OffSeed Xi)
    (HL : Row012ExtraLin s (w0At m s)) :
    Row012ConvolutionAtRev s (s.ρ) (w0At m s) := by
  have H0 : Row0ConvolutionAtRev s (s.ρ) (w0At m s) :=
    row0ConvolutionAtRev_w0At_fromAnalytic (m := m) (s := s)
  exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
    (s := s) (z := s.ρ) (w := w0At m s) H0 HL

/-- Reduction target: Row012 stencil at wp2At from analytic + two linear constraints. -/
theorem row012ConvolutionAtRev_wp2At_fromAnalytic_of_extraLin
    (m : ℕ) (s : OffSeed Xi)
    (HL : Row012ExtraLin s (wp2At m s)) :
    Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  have H0 : Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
    row0ConvolutionAtRev_wp2At_fromAnalytic (m := m) (s := s)
  exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
    (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H0 HL

/-- Reduction target: Row012 stencil at wp3At from analytic + two linear constraints. -/
theorem row012ConvolutionAtRev_wp3At_fromAnalytic_of_extraLin
    (m : ℕ) (s : OffSeed Xi)
    (HL : Row012ExtraLin s (wp3At m s)) :
    Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  have H0 : Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
    row0ConvolutionAtRev_wp3At_fromAnalytic (m := m) (s := s)
  exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
    (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) H0 HL

end XiPacket
end Targets
end Hyperlocal
