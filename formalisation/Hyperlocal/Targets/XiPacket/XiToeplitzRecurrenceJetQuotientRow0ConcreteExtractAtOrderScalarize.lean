/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize.lean

  Pure algebra helper layer (cycle-safe):

  Provide the *scalar* (row0Sigma) form of the AtOrder row--0 Toeplitz
  annihilation obligations for the jet-pivot windows `w0At/wp2At/wp3At`.

  NOTE (Lean 4.23):
  keep everything def/theorem-level; avoid Prop→Type coercions.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Scalarize

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Hyperlocal.Transport

/-! ### Scalar goal bundle at order m -/

/--
Scalar (row0Sigma) obligations equivalent to the AtOrder Toeplitz row--0 obligations.
-/
structure XiJetQuotRow0ScalarGoalsAtOrder (m : ℕ) (s : OffSeed Xi) : Type where
  hw0At  : row0Sigma s (w0At m s)  = 0
  hwp2At : row0Sigma s (wp2At m s) = 0
  hwp3At : row0Sigma s (wp3At m s) = 0

/-! ### Constructive equivalence with the Type-level AtOrder witness -/

/-- Type-level AtOrder witness ⇒ scalar goals (pure rewriting). -/
def scalarGoalsAtOrder_of_extract (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0ConcreteExtractAtOrder m s → XiJetQuotRow0ScalarGoalsAtOrder m s := by
  intro E
  refine ⟨?_, ?_, ?_⟩
  ·
    -- toeplitzL row-0 = row0Sigma
    have h := toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)
    simpa [h] using E.hop_w0At
  ·
    have h := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)
    simpa [h] using E.hop_wp2At
  ·
    have h := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)
    simpa [h] using E.hop_wp3At

/-- Scalar goals ⇒ Type-level AtOrder witness (pure rewriting). -/
def extractAtOrder_of_scalarGoals (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0ScalarGoalsAtOrder m s → XiJetQuotRow0ConcreteExtractAtOrder m s := by
  intro G
  refine ⟨?_, ?_, ?_⟩
  ·
    have h := toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)
    simpa [h] using G.hw0At
  ·
    have h := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)
    simpa [h] using G.hwp2At
  ·
    have h := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)
    simpa [h] using G.hwp3At

/--
Convenience constructor:
if you can prove the three scalar identities `row0Sigma s (w?At m s) = 0`,
you immediately obtain the Type-level AtOrder extraction witness.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_of_row0Sigma
    (m : ℕ) (s : OffSeed Xi)
    (hw0At  : row0Sigma s (w0At m s)  = 0)
    (hwp2At : row0Sigma s (wp2At m s) = 0)
    (hwp3At : row0Sigma s (wp3At m s) = 0) :
    XiJetQuotRow0ConcreteExtractAtOrder m s := by
  exact extractAtOrder_of_scalarGoals (m := m) (s := s) ⟨hw0At, hwp2At, hwp3At⟩



end XiPacket
end Targets
end Hyperlocal
