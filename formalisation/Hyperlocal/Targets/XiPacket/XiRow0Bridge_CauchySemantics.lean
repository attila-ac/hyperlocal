/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchySemantics.lean

  Row-0 bridge helper layer (pure algebra + a precise semantic hypothesis).

  IMPORTANT DESIGN RULE (cycle breaker):
  This file must remain *semantic + algebra only*.
  It MUST NOT import any Row0Semantics / Row0ConcreteProof / Toeplitz-recurrence proof modules.

  What this file provides:
    • `JetConvolutionAt` : Prop boundary for the Cauchy-normalised jet semantics.
    • `row0Sigma`        : the row-0 σ-linear form (defined locally to avoid missing identifiers).
    • `row0Sigma_eq_convCoeff` : pure algebra statement identifying `row0Sigma` as `convCoeff` at index 2.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Cancellation.Recurrence
import Mathlib.Tactic
import Hyperlocal.Targets.XiPacket.XiJet3Defs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Polynomial
open Hyperlocal.Cancellation

/-! ### Jet + convolution semantics (precise Prop boundary) -/

/-! ### Jet + convolution semantics (precise Prop boundary) -/

/-
Cycle-safe, minimal semantic gate: only the order 0/1/2 Leibniz payload.
This is exactly what Route-L produces and exactly what Row-0 needs.
-/
def JetConvolutionAt (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    -- order 0
    Xi z = (Hyperlocal.Factorization.Rρk s.ρ 1).eval z * (w 0) ∧
    -- order 1
    deriv Xi z =
      deriv (fun t => (Hyperlocal.Factorization.Rρk s.ρ 1).eval t) z * (w 0)
        + (Hyperlocal.Factorization.Rρk s.ρ 1).eval z * (w 1) ∧
    -- order 2
    deriv (deriv Xi) z =
      deriv (deriv (fun t => (Hyperlocal.Factorization.Rρk s.ρ 1).eval t)) z * (w 0)
        + (2 : ℂ) * (deriv (fun t => (Hyperlocal.Factorization.Rρk s.ρ 1).eval t) z) * (w 1)
        + (Hyperlocal.Factorization.Rρk s.ρ 1).eval z * (w 2)

/-! ### Pure algebra: `row0Sigma` as `convCoeff` at index `2` -/

/--
Row-0 σ-linear form on a Window-3 jet.

Defined *locally* to avoid missing-identifier issues and to keep this file cycle-safe.
Orientation is chosen so that it matches the existing downstream usage:

  `-(2)*w₂ + σ₂*w₁ - σ₃*w₀`.
-/
def row0Sigma (s : OffSeed Xi) (w : Transport.Window 3) : ℂ :=
  (-(2 : ℂ)) * (w 2) + (JetQuotOp.σ2 s : ℂ) * (w 1) + (-(JetQuotOp.σ3 s : ℂ)) * (w 0)

/-- Kernel coefficient sequence for row-0, in the orientation matching `row0Sigma`. -/
def row0CoeffSeq (s : OffSeed Xi) : ℕ → ℂ
  | 0 => (-(2 : ℂ))
  | 1 => (JetQuotOp.σ2 s : ℂ)
  | 2 => (-(JetQuotOp.σ3 s : ℂ))
  | _ => 0

/-- Zero-padded window coefficient sequence. -/
def winSeq (w : Transport.Window 3) : ℕ → ℂ
  | 0 => w 0
  | 1 => w 1
  | 2 => w 2
  | _ => 0

/--
`row0Sigma` is exactly `convCoeff` at index `2` with kernel `row0CoeffSeq`.

This is a *pure algebra* identity.
-/
theorem row0Sigma_eq_convCoeff (s : OffSeed Xi) (w : Transport.Window 3) :
    row0Sigma s w = convCoeff (row0CoeffSeq s) (winSeq w) 2 := by
  classical
  -- Unfold convCoeff at n=2 and expand the finite sum over `range 3 = {0,1,2}`.
  -- The remaining work is ring-normalisation.
  simp [row0Sigma, convCoeff, row0CoeffSeq, winSeq, Finset.range_succ, Finset.sum_insert,
    Finset.mem_range]
  ring_nf

end XiPacket
end Targets
end Hyperlocal
