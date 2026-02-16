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

/-- A length-3 jet window for a function `F` at center `z`. -/
def IsJet3At (F : ℂ → ℂ) (z : ℂ) (w : Transport.Window 3) : Prop :=
  w 0 = F z ∧
  w 1 = deriv F z ∧
  w 2 = deriv (deriv F) z

/--
`JetConvolutionAt` as a *Prop* (so: use `∃` for data).
This fixes the “field must be a proof” error.
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

/-- Kernel coefficient sequence for row-0. -/
def row0CoeffSeq (s : OffSeed Xi) : ℕ → ℂ
  | 0 => (-2 : ℂ)
  | 1 => JetQuotOp.σ2 s
  | 2 => (-JetQuotOp.σ3 s)
  | _ => 0

/-- Zero-padded window coefficient sequence. -/
def winSeq (w : Transport.Window 3) : ℕ → ℂ
  | 0 => w 0
  | 1 => w 1
  | 2 => w 2
  | _ => 0

theorem row0Sigma_eq_convCoeff (s : OffSeed Xi) (w : Transport.Window 3) :
    row0Sigma s w = convCoeff (row0CoeffSeq s) (winSeq w) 2 := by
  classical
  -- IMPORTANT: do NOT mention `coeff` in simp args; it is not a Prop simp lemma here.
  simp [row0Sigma, convCoeff, row0CoeffSeq, winSeq, Finset.sum_range_succ]
  ring

/-- Core reduction: once the Cauchy-product jet semantics is supplied, the bridge is pure algebra. -/
theorem row0Sigma_eq_from_JetConvolution
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : JetConvolutionAt s z w) :
    row0Sigma s w = (Rquartet s.ρ).eval z := by
  classical
  -- unpack the semantic hypothesis
  rcases H with ⟨G, hfac, hjet, Hconv⟩
  -- At this point you should:
  --  (1) use `row0Sigma_eq_convCoeff` to turn LHS into `convCoeff ... 2`
  --  (2) use `recurrence_coeff_k` (or your existing extraction lemma) with `Hconv`
  --      to rewrite that `convCoeff` into a known coefficient of `Xi` (or of `(R*G)`),
  --  (3) reduce to polynomial evaluation at `z`.
  --
  -- The remaining work depends on the exact lemma names you already have connecting
  -- `JetQuotOp.σ2/σ3` with `Rquartet.coeff 1/2` (or σ-sums ↔ coeffs).
  admit

axiom jetConv_w0  : ∀ s, JetConvolutionAt s (s.ρ)                  (w0 s)
axiom jetConv_wc  : ∀ s, JetConvolutionAt s (1 - s.ρ)              (wc s)
axiom jetConv_wp2 : ∀ s, JetConvolutionAt s ((starRingEnd ℂ) s.ρ)   (wp2 s)
axiom jetConv_wp3 : ∀ s, JetConvolutionAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s)

theorem row0Sigma_w0_eq_eval  (s : OffSeed Xi) :
    row0Sigma s (w0 s) = (Rquartet s.ρ).eval (s.ρ) := by
  exact row0Sigma_eq_from_JetConvolution s (s.ρ) (w0 s) (jetConv_w0 s)

theorem row0Sigma_wc_eq_eval  (s : OffSeed Xi) :
    row0Sigma s (wc s) = (Rquartet s.ρ).eval (1 - s.ρ) := by
  exact row0Sigma_eq_from_JetConvolution s (1 - s.ρ) (wc s) (jetConv_wc s)

theorem row0Sigma_wp2_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wp2 s) = (Rquartet s.ρ).eval ((starRingEnd ℂ) s.ρ) := by
  exact row0Sigma_eq_from_JetConvolution s ((starRingEnd ℂ) s.ρ) (wp2 s) (jetConv_wp2 s)

theorem row0Sigma_wp3_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wp3 s) = (Rquartet s.ρ).eval (1 - (starRingEnd ℂ) s.ρ) := by
  exact row0Sigma_eq_from_JetConvolution s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) (jetConv_wp3 s)

end XiPacket
end Targets
end Hyperlocal
