/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyProductAttempt.lean

  Cauchy-product attempt (cycle-safe enough for now):
  discharge the Row--0 scalar goal from a *Convolution* hypothesis.

  IMPORTANT:
  We introduce a NEW semantic gate name `JetConvolutionAtRev` which is genuinely
  a `Convolution` statement, to avoid clashes with existing names in the repo.

  This file is intended to be pasted on-disk exactly, so Lake builds *this* content.
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

/-- `JetConvolutionAtRev` is the *Convolution* semantic gate (as a Prop). -/
def JetConvolutionAtRev (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    Convolution
      (row0CoeffSeqRev s)
      (winSeqRev w)
      (fun n =>
        match n with
        | 0 => Xi z
        | 1 => deriv Xi z
        | 2 => deriv (deriv Xi) z
        | _ => 0)

/--
Pure algebra: `row0Sigma` equals the `n=3` Cauchy coefficient of the reverse convolution.
-/
theorem row0Sigma_eq_convCoeff_rev (s : OffSeed Xi) (w : Transport.Window 3) :
    row0Sigma s w = convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 := by
  classical
  simp [convCoeff, row0Sigma, row0CoeffSeqRev, winSeqRev,
        Finset.range_succ, Finset.sum_range_succ]
  ring_nf

/-- Core discharge: `JetConvolutionAtRev` implies `row0Sigma = 0`. -/
theorem row0Sigma_eq_zero_from_JetConvolutionRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : JetConvolutionAtRev s z w) :
    row0Sigma s w = 0 := by
  classical
  rcases H with ⟨G, hfac, hjet, Hconv⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 := by
    simpa using (Hconv 3)
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w)] using h3

/-
Temporary semantic axioms (to be discharged later).
-/
axiom jetConv_w0  : ∀ s, JetConvolutionAtRev s (s.ρ)                    (w0 s)
axiom jetConv_wc  : ∀ s, JetConvolutionAtRev s (1 - s.ρ)                (wc s)
axiom jetConv_wp2 : ∀ s, JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ)     (wp2 s)
axiom jetConv_wp3 : ∀ s, JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s)

/-- These are now the *actual Row--0 scalar goals*. -/
theorem row0Sigma_w0_eq_zero  (s : OffSeed Xi) : row0Sigma s (w0 s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_eq_zero_from_JetConvolutionRev
    s (s.ρ) (w0 s) (jetConv_w0 s)

theorem row0Sigma_wc_eq_zero  (s : OffSeed Xi) : row0Sigma s (wc s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_eq_zero_from_JetConvolutionRev
    s (1 - s.ρ) (wc s) (jetConv_wc s)

theorem row0Sigma_wp2_eq_zero (s : OffSeed Xi) : row0Sigma s (wp2 s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_eq_zero_from_JetConvolutionRev
    s ((starRingEnd ℂ) s.ρ) (wp2 s) (jetConv_wp2 s)

theorem row0Sigma_wp3_eq_zero (s : OffSeed Xi) : row0Sigma s (wp3 s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_eq_zero_from_JetConvolutionRev
    s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) (jetConv_wp3 s)

/-- Optional: keep “= eval” statements as corollaries using `R_quartet_zeros`. -/
theorem row0Sigma_w0_eq_eval  (s : OffSeed Xi) :
    row0Sigma s (w0 s) = (Rquartet s.ρ).eval (s.ρ) := by
  have hz : (Rquartet s.ρ).eval (s.ρ) = 0 := (R_quartet_zeros s).1
  simpa [row0Sigma_w0_eq_zero (s := s), hz]

theorem row0Sigma_wc_eq_eval  (s : OffSeed Xi) :
    row0Sigma s (wc s) = (Rquartet s.ρ).eval (1 - s.ρ) := by
  have hz : (Rquartet s.ρ).eval (1 - s.ρ) = 0 := (R_quartet_zeros s).2.2.1
  simpa [row0Sigma_wc_eq_zero (s := s), hz]

theorem row0Sigma_wp2_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wp2 s) = (Rquartet s.ρ).eval ((starRingEnd ℂ) s.ρ) := by
  have hz0 : (Rquartet s.ρ).eval (star s.ρ) = 0 := (R_quartet_zeros s).2.1
  have hz : (Rquartet s.ρ).eval ((starRingEnd ℂ) s.ρ) = 0 := by
    simpa using hz0
  simpa [row0Sigma_wp2_eq_zero (s := s), hz]

theorem row0Sigma_wp3_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wp3 s) = (Rquartet s.ρ).eval (1 - (starRingEnd ℂ) s.ρ) := by
  have hz0 : (Rquartet s.ρ).eval (1 - star s.ρ) = 0 := (R_quartet_zeros s).2.2.2
  have hz : (Rquartet s.ρ).eval (1 - (starRingEnd ℂ) s.ρ) = 0 := by
    simpa using hz0
  simpa [row0Sigma_wp3_eq_zero (s := s), hz]

/- Bulletproof visibility: export the key names explicitly. -/
namespace CauchyProductAttemptExport
export _root_.Hyperlocal.Targets.XiPacket
  (JetConvolutionAtRev
   row0Sigma_eq_convCoeff_rev
   row0Sigma_eq_zero_from_JetConvolutionRev
   row0Sigma_w0_eq_zero
   row0Sigma_wc_eq_zero
   row0Sigma_wp2_eq_zero
   row0Sigma_wp3_eq_zero
   row0Sigma_w0_eq_eval
   row0Sigma_wc_eq_eval
   row0Sigma_wp2_eq_eval
   row0Sigma_wp3_eq_eval)
end CauchyProductAttemptExport

end XiPacket
end Targets
end Hyperlocal
