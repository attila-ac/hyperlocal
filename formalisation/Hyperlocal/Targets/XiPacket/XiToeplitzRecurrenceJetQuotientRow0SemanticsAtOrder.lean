/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  AtOrder Route–B semantics (public surface).

  Definitions are in:
    XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs.lean

  CLEAN PUBLIC-WRAPPER RETARGET:

  The support chain below is already clean:
    * rec2_w0At_trueAnalytic / rec2_wp2At_trueAnalytic / rec2_wp3At_trueAnalytic
    * xiJetQuotOpZeroAtOrder_of_rec2
    * xiJetQuotRow0WitnessCAtOrder_of_opZero

  So the public wrapper should build the bundled Rec2 payload directly and avoid
  any local sigma/coords/provider instance installation. This keeps the wrapper
  proof term off the historical provider-facing route that still drags the old
  coords01 stub into the final cone.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Route–B recurrence-natural semantic output.

CRITICAL:
Do not install local sigma/coords/provider instances here.
Build the bundled Rec2 payload directly from the clean true-analytic Rec2 lemmas,
then pass it to the clean theorem `xiJetQuotOpZeroAtOrder_of_rec2`.
-/
theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  letI : XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by infer_instance
  have Hrec : XiJetQuotRec2AtOrder m s := by
    refine ⟨?_, ?_, ?_⟩
    · exact rec2_w0At_trueAnalytic (m := m) (s := s)
    · exact rec2_wp2At_trueAnalytic (m := m) (s := s)
    · exact rec2_wp3At_trueAnalytic (m := m) (s := s)
  exact xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

/-- Derived row-0 witness bundle (projection of the full-window contract). -/
noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
