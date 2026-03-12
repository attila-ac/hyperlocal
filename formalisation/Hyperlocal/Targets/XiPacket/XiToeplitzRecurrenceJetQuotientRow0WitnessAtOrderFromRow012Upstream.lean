/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream.lean

  Theorem-level row-0 witness at order, sourced from the Row012-upstream
  recurrence route.

  CYCLE DISCIPLINE:
  * consume only provider surfaces here
  * keep the sigma side on the historical DAG-clean fallback surface
  * keep the coords01 side on the DAG-clean axiom provider surface
  * do NOT import the theorem coords01 installer, because that installer
    currently routes through the analytic extractor corridor and closes a cycle
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Type-valued row-0 witness package derived from the Row012-upstream recurrence
route, by feeding the explicit Rec2 payload directly into the clean Row0
semantic theorem.
-/
noncomputable def xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical

  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  exact
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
      (xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec)

end XiPacket
end Targets
end Hyperlocal
