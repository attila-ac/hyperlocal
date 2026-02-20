/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs.lean

  AtOrder Route–B semantics (definitions only).

  This file is intentionally axiom-free and contains only:

  * Prop-level contract `XiJetQuotOpZeroAtOrder m s` (full Window-3 annihilation)
  * Type-level row-0 witness `XiJetQuotRow0WitnessCAtOrder m s`
  * helper `xiJetQuotRow0WitnessCAtOrder_of_opZero`

  IMPORTANT:
  This file MUST actually declare the symbols under
    `Hyperlocal.Targets.XiPacket`
  so downstream `_root_.Hyperlocal.Targets.XiPacket....` resolves.
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

/-- Raw recurrence-natural semantic output (AtOrder, full Window-3 annihilation). -/
structure XiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  hop_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  = 0
  hop_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) = 0
  hop_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) = 0

/--
Type-level row-0 projection witness:
`toeplitzL 2 (JetQuotOp.aRk1 s)` annihilates row 0 of the AtOrder windows.
-/
structure XiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) : Type where
  hop_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0
  hop_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0
  hop_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

/-- Row-0 witness derived from a supplied full-window annihilation proof. -/
noncomputable def xiJetQuotRow0WitnessCAtOrder_of_opZero (m : ℕ) (s : OffSeed Xi)
    (H : XiJetQuotOpZeroAtOrder m s) : XiJetQuotRow0WitnessCAtOrder m s := by
  classical
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
