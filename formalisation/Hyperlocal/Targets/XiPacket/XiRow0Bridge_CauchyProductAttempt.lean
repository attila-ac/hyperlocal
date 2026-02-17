/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyProductAttempt.lean

  Cauchy-product attempt (cycle-safe enough for now):
  discharge the Row--0 scalar goal from a *Convolution* hypothesis.

  IMPORTANT (fixing the failures you hit):
  * Do NOT redeclare `JetConvolutionAt` (it already exists in `...CauchySemantics` and
    in this repo it is a Leibniz payload, not a `Convolution` function).
  * Therefore, in this file we introduce a NEW semantic gate name
      `JetConvolutionAtRev`
    which is genuinely a `Convolution` statement.

  Key point:
  To match `row0Sigma s w = (-2)*w2 + σ2*w1 + (-σ3)*w0`,
  we feed the window into the convolution in *reverse order*:
    b0 = w2, b1 = w1, b2 = w0.
  Then the n=3 Cauchy coefficient is exactly row0Sigma, provided we choose the
  kernel coefficients appropriately.

  This file keeps the four `jetConv_*` as axioms for now; once you prove them,
  the Toeplitz Row--0 arm becomes theorem-level.
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
  | 0 => w 2
  | 1 => w 1
  | 2 => w 0
  | _ => 0

/--
Kernel coefficient sequence for Row--0 in the *reverse-padding* convention:

We want:
  convCoeff a (winSeqRev w) 3
    = (-2)*w2 + σ2*w1 + (-σ3)*w0.

Since
  convCoeff a b 3 = Σ i=0..3 a i * b (3-i)
and `b 0 = w2`, `b 1 = w1`, `b 2 = w0`, `b 3 = 0`,
it suffices to set:
  a 3 = -2, a 2 = σ2, a 1 = -σ3, a 0 = 0.
-/
def row0CoeffSeqRev (s : OffSeed Xi) : ℕ → ℂ
  | 0 => 0
  | 1 => (-JetQuotOp.σ3 s)
  | 2 => (JetQuotOp.σ2 s)
  | 3 => (-2 : ℂ)
  | _ => 0

/--
`JetConvolutionAtRev` is the *Convolution* semantic gate (as a Prop).

This avoids the name-clash with the existing `JetConvolutionAt` in
`XiRow0Bridge_CauchySemantics.lean` (which, in this repo, is a Leibniz payload).
-/
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
Pure algebra: `row0Sigma` is exactly the `n=3` convolution coefficient of
`row0CoeffSeqRev` with `winSeqRev`.

No `Rquartet.coeff` lemmas are needed.
-/
theorem row0Sigma_eq_convCoeff_rev (s : OffSeed Xi) (w : Transport.Window 3) :
    row0Sigma s w = convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 := by
  classical
  -- Expand convCoeff at n=3, and observe only i=1,2,3 contribute.
  simp [convCoeff, row0Sigma, row0CoeffSeqRev, winSeqRev,
        Finset.range_succ, Finset.sum_range_succ]
  ring

/--
Core discharge: from `JetConvolutionAtRev` we get the `n=3` coefficient equals `0`
(because the RHS sequence is padded to 0 beyond order 2), hence `row0Sigma = 0`.
-/
theorem row0Sigma_eq_zero_from_JetConvolutionRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : JetConvolutionAtRev s z w) :
    row0Sigma s w = 0 := by
  classical
  rcases H with ⟨G, hfac, hjet, Hconv⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 := by
    -- Convolution gives equality for all n; at n=3 the RHS is definitional 0.
    simpa using (Hconv 3)
  -- Rewrite convCoeff into row0Sigma using the pure algebra lemma.
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w)] using h3

/-
Temporary semantic axioms (to be discharged later).
They should be proved from your analytic layer once you wire the Cauchy/Taylor normalisation.
-/
axiom jetConv_w0  : ∀ s, JetConvolutionAtRev s (s.ρ)                      (w0 s)
axiom jetConv_wc  : ∀ s, JetConvolutionAtRev s (1 - s.ρ)                  (wc s)
axiom jetConv_wp2 : ∀ s, JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ)       (wp2 s)
axiom jetConv_wp3 : ∀ s, JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ)   (wp3 s)

/-- These are now the *actual Row--0 scalar goals*. -/
theorem row0Sigma_w0_eq_zero  (s : OffSeed Xi) : row0Sigma s (w0 s) = 0 :=
  row0Sigma_eq_zero_from_JetConvolutionRev s (s.ρ) (w0 s) (jetConv_w0 s)

theorem row0Sigma_wc_eq_zero  (s : OffSeed Xi) : row0Sigma s (wc s) = 0 :=
  row0Sigma_eq_zero_from_JetConvolutionRev s (1 - s.ρ) (wc s) (jetConv_wc s)

theorem row0Sigma_wp2_eq_zero (s : OffSeed Xi) : row0Sigma s (wp2 s) = 0 :=
  row0Sigma_eq_zero_from_JetConvolutionRev s ((starRingEnd ℂ) s.ρ) (wp2 s) (jetConv_wp2 s)

theorem row0Sigma_wp3_eq_zero (s : OffSeed Xi) : row0Sigma s (wp3 s) = 0 :=
  row0Sigma_eq_zero_from_JetConvolutionRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) (jetConv_wp3 s)

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

end XiPacket
end Targets
end Hyperlocal
