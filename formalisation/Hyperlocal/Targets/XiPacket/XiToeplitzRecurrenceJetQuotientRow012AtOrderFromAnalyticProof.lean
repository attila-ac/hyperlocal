/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalyticProof.lean

  Cycle-safe placeholder proof module.

  This file exists only to provide the symbol
    xiJetQuotRow012AtOrder_fromAnalytic_proof

  without importing the analytic pipeline (which would reintroduce cycles).
  Later, replace the axiom by the real construction.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Cycle-safe placeholder for the Type-valued analytic landing spot.

Replace this proof term by the real analytic construction once the analytic extraction
is available without importing Row0Semantics / SequenceAtOrderRecurrenceA.
-/
noncomputable def xiJetQuotRow012AtOrder_fromAnalytic_proof
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s := by
  classical

  -- full-window contract
  have H0 : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder (m := m) (s := s)

  -- row-0 bundle
  have hrow0 : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) H0

  -- row-1 / row-2 projections for each AtOrder window
  have hw0_1 : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (1 : Fin 3) = 0 := by
    simpa using congrArg (fun w => w (1 : Fin 3)) H0.hop_w0At
  have hw0_2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (2 : Fin 3) = 0 := by
    simpa using congrArg (fun w => w (2 : Fin 3)) H0.hop_w0At

  have hwp2_1 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (1 : Fin 3) = 0 := by
    simpa using congrArg (fun w => w (1 : Fin 3)) H0.hop_wp2At
  have hwp2_2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (2 : Fin 3) = 0 := by
    simpa using congrArg (fun w => w (2 : Fin 3)) H0.hop_wp2At

  have hwp3_1 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (1 : Fin 3) = 0 := by
    simpa using congrArg (fun w => w (1 : Fin 3)) H0.hop_wp3At
  have hwp3_2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (2 : Fin 3) = 0 := by
    simpa using congrArg (fun w => w (2 : Fin 3)) H0.hop_wp3At

  exact
    { h0 := hrow0
      h1_w0At := hw0_1
      h2_w0At := hw0_2
      h1_wp2At := hwp2_1
      h2_wp2At := hwp2_2
      h1_wp3At := hwp3_1
      h2_wp3At := hwp3_2 }

end XiPacket
end Targets
end Hyperlocal
