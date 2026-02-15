/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteProof.lean

  NEXT STEP (no refactor, pure semantic burden reduction):

  Reduce `XiJetQuotRow0WitnessC s` to four explicit scalar ℂ-identities by:
  * expanding row-0 of `toeplitzL 2 (JetQuotOp.aRk1 s)`,
  * unfolding `JetQuotOp.aRk1 s 0/1/2` as `(-σ3, σ2, -2)`.

  NOTE: `XiJetQuotRow0WitnessC s` is a `Type` (structure with Prop-fields),
  so we do not state a direct `↔`. Instead we provide:
    * `scalarGoals_of_witnessC : WitnessC → ScalarGoals`
    * `witnessC_of_scalarGoals : ScalarGoals → WitnessC`
    * `Nonempty WitnessC ↔ Nonempty ScalarGoals` (Prop-level iff)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic


set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3

/-! ## Row-0 explicit scalarization for the jet-quotient Toeplitz operator -/

/-- The row-0 3-term scalar expression using the raw coefficients `aRk1`. -/
def row0Expr (s : Hyperlocal.OffSeed Xi) (w : Window 3) : ℂ :=
  ((JetQuotOp.aRk1 s 0) * w (0 : Fin 3) + (JetQuotOp.aRk1 s 1) * w (1 : Fin 3))
    + (JetQuotOp.aRk1 s 2) * w (2 : Fin 3)

/-- The fully-unfolded row-0 scalar expression with coefficients `(-σ3, σ2, -2)`. -/
def row0Sigma (s : Hyperlocal.OffSeed Xi) (w : Window 3) : ℂ :=
  ((-(JetQuotOp.σ3 s : ℂ)) * w (0 : Fin 3) + (JetQuotOp.σ2 s : ℂ) * w (1 : Fin 3))
    + (-(2 : ℂ)) * w (2 : Fin 3)

/-- Unfold the three `aRk1` values used in row 0: `(-σ3, σ2, -2)`. -/
lemma row0Expr_eq_row0Sigma (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    row0Expr s w = row0Sigma s w := by
  have hz0 : JetQuotOp.aRk1 s 0 = (-(JetQuotOp.σ3 s : ℂ)) := by
    simp [JetQuotOp.aRk1, JetQuotOp.aR]
  have hz1 : JetQuotOp.aRk1 s 1 = (JetQuotOp.σ2 s : ℂ) := by
    simp [JetQuotOp.aRk1, JetQuotOp.aR]
  have hz2 : JetQuotOp.aRk1 s 2 = (-(2 : ℂ)) := by
    simpa using (JetQuotOp.aRk1_nat2_eq_neg_two (s := s))
  simp [row0Expr, row0Sigma, hz0, hz1, hz2, add_assoc, add_left_comm, add_comm]

/--
Row-0 of `toeplitzL 2 (aRk1 s)` is exactly `row0Expr s w`.

This is purely algebraic rewriting via the existing expander
`toeplitzL_two_apply_fin0` (argument name is `coeffs`).
-/
lemma toeplitzL_row0_eq_row0Expr (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = row0Expr s w := by
  simpa [row0Expr] using
    (toeplitzL_two_apply_fin0 (coeffs := JetQuotOp.aRk1 s) (w := w))

/--
Row-0 of `toeplitzL 2 (aRk1 s)` is exactly the explicit `row0Sigma` expression.
-/
lemma toeplitzL_row0_eq_row0Sigma (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = row0Sigma s w := by
  simpa [toeplitzL_row0_eq_row0Expr (s := s) (w := w), row0Expr_eq_row0Sigma (s := s) (w := w)]

/-!
## Scalar goal package (Type-level) and constructive equivalence with the witness bundle
-/

/--
The *scalar* obligations equivalent (constructively) to `XiJetQuotRow0WitnessC s`.

Each field is a single explicit ℂ-identity:
  `row0Sigma s w = 0`
for `w = w0, wc, wp2, wp3`.
-/
structure XiJetQuotRow0ScalarGoals (s : Hyperlocal.OffSeed Xi) : Type where
  hw0  : row0Sigma s (w0 s)  = 0
  hwc  : row0Sigma s (wc s)  = 0
  hwp2 : row0Sigma s (wp2 s) = 0
  hwp3 : row0Sigma s (wp3 s) = 0


/-- Witness bundle ⇒ scalar-goals (pure rewriting). -/
def scalarGoals_of_witnessC (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0WitnessC s → XiJetQuotRow0ScalarGoals s := by
  intro h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- hop_w0 is a toeplitzL statement, so rewrite via toeplitzL_row0_eq_row0Sigma
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0 s)] using h.hop_w0
  · simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)] using h.hop_wc
  · simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2 s)] using h.hop_wp2
  · simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3 s)] using h.hop_wp3


/-- Scalar-goals ⇒ witness bundle (pure rewriting). -/
def witnessC_of_scalarGoals (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s → XiJetQuotRow0WitnessC s := by
  intro g
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- hop_w0
    have hrew := (toeplitzL_row0_eq_row0Sigma (s := s) (w := w0 s))
    -- rewrite LHS to `row0Sigma`, then close by `g.hw0`
    simpa [hrew] using g.hw0
  · -- hop_wc
    have hrew := (toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s))
    simpa [hrew] using g.hwc
  · -- hop_wp2
    have hrew := (toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2 s))
    simpa [hrew] using g.hwp2
  · -- hop_wp3
    have hrew := (toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3 s))
    simpa [hrew] using g.hwp3

/-- Prop-level iff (Nonempty on both sides) expressing obligation equivalence. -/
theorem witnessC_nonempty_iff_scalarGoals_nonempty (s : Hyperlocal.OffSeed Xi) :
    Nonempty (XiJetQuotRow0WitnessC s) ↔ Nonempty (XiJetQuotRow0ScalarGoals s) := by
  constructor
  · intro hw
    rcases hw with ⟨h⟩
    exact ⟨scalarGoals_of_witnessC (s := s) h⟩
  · intro hg
    rcases hg with ⟨g⟩
    exact ⟨witnessC_of_scalarGoals (s := s) g⟩

end XiPacket
end Targets
end Hyperlocal
