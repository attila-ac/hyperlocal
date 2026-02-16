import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization

/-!
Row-0 analytic bridge (Route-A integration).

This file is the ONLY place where analytic ξ-inputs are consumed to discharge
row-0 scalar obligations for the Jet-Quotient Toeplitz/recurrence arm.

All downstream files remain purely algebraic.

The only remaining ξ-semantic gate is the *coefficient identity* that relates the
algebraic row-0 sum `row0Sigma` on each canonical ξ-window to evaluation of the
quartet polynomial `Rquartet` at the corresponding quartet point.

IMPORTANT:
* The old (too-strong) statement `∀ w z, row0Sigma s w = (Rquartet s.ρ).eval z`
  is false.
* What we need downstream are only the four canonical instances below.
-/

/-- Bridge lemma (canonical instance): `w0` at the root `ρ`. -/
axiom row0Sigma_w0_eq_eval (s : OffSeed Xi) :
  row0Sigma s (w0 s) = (Rquartet s.ρ).eval s.ρ

/-- Bridge lemma (canonical instance): `wc` at the root `1-ρ`. -/
axiom row0Sigma_wc_eq_eval (s : OffSeed Xi) :
  row0Sigma s (wc s) = (Rquartet s.ρ).eval (1 - s.ρ)

/-- Bridge lemma (canonical instance): `wp2` at the root `conj(ρ)`.

NOTE: we use `starRingEnd ℂ` to match the statement shape of `R_quartet_zeros`.
-/
axiom row0Sigma_wp2_eq_eval (s : OffSeed Xi) :
  row0Sigma s (wp2 s) = (Rquartet s.ρ).eval ((starRingEnd ℂ) s.ρ)

/-- Bridge lemma (canonical instance): `wp3` at the root `1-conj(ρ)`. -/
axiom row0Sigma_wp3_eq_eval (s : OffSeed Xi) :
  row0Sigma s (wp3 s) = (Rquartet s.ρ).eval (1 - (starRingEnd ℂ) s.ρ)

/-- Route-A: analytic discharge of the row-0 scalar goals (modulo the bridge axioms). -/
noncomputable def xiJetQuot_row0_scalarGoals_analytic (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 := by
    rw [row0Sigma_w0_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).1
  hwc := by
    rw [row0Sigma_wc_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).2.2.1
  hwp2 := by
    rw [row0Sigma_wp2_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).2.1
  hwp3 := by
    rw [row0Sigma_wp3_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).2.2.2

/-- Public stable name (consumed downstream). -/
noncomputable def xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s :=
  xiJetQuot_row0_scalarGoals_analytic s

end XiPacket
end Targets
end Hyperlocal
