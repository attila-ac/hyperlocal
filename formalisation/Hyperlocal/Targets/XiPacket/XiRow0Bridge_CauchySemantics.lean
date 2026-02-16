/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchySemantics.lean

  Row-0 bridge helper layer (pure algebra + a precise semantic hypothesis).

  This file is intentionally independent of the downstream Toeplitz/recurrence plumbing.
  It provides:
    * a robust, type-correct statement of the missing semantic content as a Prop
      (`JetConvolutionAt`), avoiding `structure ... : Prop` projection issues;
    * the purely algebraic identity `row0Sigma = convCoeff ... 2`.

  The final goal (to remove all semantic axioms) is to prove `JetConvolutionAt`
  from analytic Taylor/product facts and the Route-A factorisation interface.
-/

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

/-! ### Jet + convolution semantics (precise Prop boundary) -/

/-- A length-3 jet window for a function `F` at center `z`. -/
def IsJet3At (F : ℂ → ℂ) (z : ℂ) (w : Transport.Window 3) : Prop :=
  w 0 = F z ∧
  w 1 = deriv F z ∧
  w 2 = deriv (deriv F) z

/--
`JetConvolutionAt` as a *Prop* (data carried via `∃`).

This avoids the Lean error “field must be a proof” that occurs when trying to put
non-proof fields into a `structure ... : Prop`.

Intended reading:
* There exists a Route-A factor `G` with `Xi = Rquartet * G` (via `FactorisedByQuartet`).
* `w` is the jet `[G(z), G'(z), G''(z)]`.
* At the coefficient level the Cauchy product of `Rquartet.coeff` with the (zero-padded)
  jet window reproduces the (zero-padded) jet of `Xi` at `z`.
-/
def JetConvolutionAt (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    Convolution
      (fun n => (Rquartet s.ρ).coeff n)
      (fun n =>
        match n with
        | 0 => w 0
        | 1 => w 1
        | 2 => w 2
        | _ => 0)
      (fun n =>
        match n with
        | 0 => Xi z
        | 1 => deriv Xi z
        | 2 => deriv (deriv Xi) z
        | _ => 0)

/-! ### Pure algebra: `row0Sigma` is `convCoeff` at index `2` -/

/-- Kernel coefficient sequence for row-0, in the orientation matching `row0Sigma`. -/
def row0CoeffSeq (s : OffSeed Xi) : ℕ → ℂ
  | 0 => (-2 : ℂ)
  | 1 => (JetQuotOp.σ2 s : ℂ)
  | 2 => (-(JetQuotOp.σ3 s : ℂ))
  | _ => 0

/-- Zero-padded window coefficient sequence. -/
def winSeq (w : Transport.Window 3) : ℕ → ℂ
  | 0 => w 0
  | 1 => w 1
  | 2 => w 2
  | _ => 0

/-- `row0Sigma` is exactly `convCoeff` at index `2` with the kernel `row0CoeffSeq`. -/
theorem row0Sigma_eq_convCoeff (s : OffSeed Xi) (w : Transport.Window 3) :
    row0Sigma s w = convCoeff (row0CoeffSeq s) (winSeq w) 2 := by
  classical
  simp [row0Sigma, convCoeff, row0CoeffSeq, winSeq, Finset.range_succ, Finset.sum_insert,
    Finset.mem_range, Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm]
  -- ring   -- delete this line (simp already solved it)


end XiPacket
end Targets
end Hyperlocal
