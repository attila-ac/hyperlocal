/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream.lean

  Theorem-level row-0 witness at order, sourced from the Row012-upstream
  recurrence route.

  IMPORTANT DIAGNOSTIC OUTCOME:
  Do NOT try to synthesize
      [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
  locally in this file.

  Reason:
  the available producer route in this cone is conditional / cyclic on the
  true-analytic side, so asking for it here pulls this file into the Row012
  true-analytic adapter cycle.

  Therefore this file stays consumer-side:
  * restore only the healthy sigma/coords producer surfaces at this boundary,
  * obtain the explicit Rec2 payload from the Row012-upstream theorem,
  * feed that payload directly into `xiJetQuotOpZeroAtOrder_of_rec2`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream

-- restore only the healthy producer surfaces needed by
-- `xiJetQuotRec2AtOrder_fromRow012Upstream`
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

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
