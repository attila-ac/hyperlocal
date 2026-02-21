/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyProductAttempt.lean

  Cauchy-product bridge (cycle-safe):
  discharge the Row--0 scalar goal from a *Convolution* hypothesis.

  IMPORTANT:
  We introduce a NEW semantic gate name `JetConvolutionAtRev` which is genuinely
  a (tail) convolution statement, to avoid clashes with existing names in the repo.

  MOVE-1 (2026-02-18):
  Add the *minimal* Row--0 semantic gate `Row0ConvolutionAtRev`, which requires
  only the single coefficient identity at n=3 that actually feeds `row0Sigma`.

  This shrinks the eventual analytic discharge obligation from:
    ∀ n, convolution coefficient identity
  down to:
    convCoeff ... 3 = 0.

  NOTE:
  This file contains **no** `jetConv_*` axioms and **no** canonical-window
  instances. Those instances live in:

    `XiRow0Bridge_CauchyConvolutionDischarge.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Cancellation.Recurrence
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Polynomial
open Hyperlocal.Cancellation

/-- Window sequence in the order that matches `row0Sigma` at coefficient `n=3`. -/
def winSeqRev (w : Transport.Window 3) : ℕ → ℂ
  | 0 => w ⟨2, by decide⟩
  | 1 => w ⟨1, by decide⟩
  | 2 => w ⟨0, by decide⟩
  | _ => 0

/--
Kernel coefficient sequence for Row--0 in the reverse-padding convention.

We want:
  convCoeff a (winSeqRev w) 3 = (-2)*w2 + σ2*w1 + (-σ3)*w0.

So set:
  a 3 = -2, a 2 = σ2, a 1 = -σ3, a 0 = 0.
-/
def row0CoeffSeqRev (s : OffSeed Xi) : ℕ → ℂ
  | 0 => 0
  | 1 => (-JetQuotOp.σ3 s)
  | 2 => (JetQuotOp.σ2 s)
  | 3 => (-2 : ℂ)
  | _ => 0

/--
`JetConvolutionAtRev` is the *tail* convolution semantic gate (as a Prop):
we only require the vanishing convolution constraints for `n ≥ 3`.

This matches the intended Route--C usage: we care only about the high-index
Cauchy coefficients (3,4,5,...) which are 0 in the canonical "jet padded by 0"
output sequence.
-/
def JetConvolutionAtRev (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    ∀ n, 3 ≤ n → convCoeff (row0CoeffSeqRev s) (winSeqRev w) n = 0

/--
`Row0ConvolutionAtRev` is the *minimal* Route--C gate needed for Row--0:
only the single coefficient identity at `n=3`.
-/
def Row0ConvolutionAtRev (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0

/--
Pure algebra: `row0Sigma` equals the `n=3` Cauchy coefficient of the reverse convolution.
-/
theorem row0Sigma_eq_convCoeff_rev (s : OffSeed Xi) (w : Transport.Window 3) :
    row0Sigma s w = convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 := by
  classical
  simp [convCoeff, row0Sigma, row0CoeffSeqRev, winSeqRev,
        Finset.range_succ, Finset.sum_range_succ]
  ring_nf

/-- Projection: full tail-convolution gate implies the minimal Row--0 gate. -/
theorem row0ConvolutionAtRev_of_JetConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    JetConvolutionAtRev s z w → Row0ConvolutionAtRev s z w := by
  classical
  intro H
  rcases H with ⟨G, hfac, hjet, Htail⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 := by
    exact Htail 3 (by decide)
  exact ⟨G, hfac, hjet, h3⟩

/-- Core discharge (full gate): `JetConvolutionAtRev` implies `row0Sigma = 0`. -/
theorem row0Sigma_eq_zero_from_JetConvolutionRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : JetConvolutionAtRev s z w) :
    row0Sigma s w = 0 := by
  classical
  have H0 : Row0ConvolutionAtRev s z w :=
    row0ConvolutionAtRev_of_JetConvolutionAtRev (s := s) (z := z) (w := w) H
  rcases H0 with ⟨G, hfac, hjet, h3⟩
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w)] using h3

/-- Core discharge (minimal gate): `Row0ConvolutionAtRev` implies `row0Sigma = 0`. -/
theorem row0Sigma_eq_zero_from_Row0ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row0ConvolutionAtRev s z w) :
    row0Sigma s w = 0 := by
  classical
  rcases H with ⟨G, hfac, hjet, h3⟩
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w)] using h3

/-! ### Re-export (core only) -/
namespace CauchyProductAttemptExport
export _root_.Hyperlocal.Targets.XiPacket
  (winSeqRev
   row0CoeffSeqRev
   JetConvolutionAtRev
   Row0ConvolutionAtRev
   row0Sigma_eq_convCoeff_rev
   row0ConvolutionAtRev_of_JetConvolutionAtRev
   row0Sigma_eq_zero_from_JetConvolutionRev
   row0Sigma_eq_zero_from_Row0ConvolutionAtRev)
end CauchyProductAttemptExport

end XiPacket
end Targets
end Hyperlocal
