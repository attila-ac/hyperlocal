/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  Route–B semantic insertion point (AtOrder, jet-pivot windows), stated in a
  recurrence-natural form and then projected to the row-0 witness.

  BIG SWEEP (2026-02-19, refined):
    We axiomatize the full Window-3 operator annihilation

      toeplitzL 2 (JetQuotOp.aRk1 s) (w0At/wp2At/wp3At) = 0

    and then *derive* the row-0 equalities as immediate projections.

  Lean 4.23 note:
    * The recurrence-natural statement is `Prop`.
    * The row-0 witness is `Type` (a concrete witness bundle), so it is provided
      by a `def`.

  Cycle-safety:
    Imports only window defs + operator coeff defs + Toeplitz operator.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Raw Route–B semantic output (AtOrder, full Window-3 annihilation). -/
structure XiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  hop_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  = 0
  hop_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) = 0
  hop_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) = 0

/--
The only genuine semantic cliff for AtOrder Route–B (recurrence-natural form).

The concrete order-`m` jet-quotient recurrence extraction theorem should prove
this statement, at which point the entire AtOrder Gate becomes axiom-free.
-/
axiom xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s

/--
Route–B semantic witness (AtOrder, row-0 projection):
`toeplitzL 2 (JetQuotOp.aRk1 s)` annihilates row 0 of the AtOrder windows.
-/
structure XiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) : Type where
  hop_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0
  hop_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0
  hop_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

/-- Row-0 witness derived from the recurrence-natural full annihilation axiom. -/
noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  have H : XiJetQuotOpZeroAtOrder m s := xiJetQuotOpZeroAtOrder (m := m) (s := s)
  refine ⟨?_, ?_, ?_⟩
  ·
    have := congrArg (fun w => w (0 : Fin 3)) H.hop_w0At
    simpa using this
  ·
    have := congrArg (fun w => w (0 : Fin 3)) H.hop_wp2At
    simpa using this
  ·
    have := congrArg (fun w => w (0 : Fin 3)) H.hop_wp3At
    simpa using this

end XiPacket
end Targets
end Hyperlocal
