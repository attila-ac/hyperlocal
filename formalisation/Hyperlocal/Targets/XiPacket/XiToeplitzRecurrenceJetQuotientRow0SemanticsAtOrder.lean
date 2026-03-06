/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  AtOrder Route–B semantics (public surface).

  Definitions are in:
    XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs.lean

  Provider refactor (2026-02-22):
  `xiJetQuotOpZeroAtOrder_fromRecurrenceA` consumes the recurrence payload via
  a typeclass `[XiJetQuotRec2AtOrderProvider]`.

  CLEAN SIGMA/COORDS RETARGET (post cycle-break):
  The public wrapper now avoids the historical sigma/stub path.

  New local route:
    * install `[XiJetQuotRec2AtOrderTrueAnalytic]` from the true-analytic
      Row012-convolution pipeline
    * derive a local clean sigma provider from
        `xiAtOrderSigmaOut_fromRec2TrueAnalytic`
    * derive a local clean coords01 provider from
        `xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic`
    * let the standard interface
        `[XiJetQuotRec2AtOrderTrueAnalytic] -> [XiJetQuotRec2AtOrderProvider]`
      feed `xiJetQuotOpZeroAtOrder_fromRecurrenceA`

  IMPORTANT:
  * do not touch shared historical provider files
  * install only local theorem-backed instances here
  * this is the direct attack on the remaining Row0 spec trio
      `xiJetQuot_row0_w0At_spec`
      `xiJetQuot_row0_wp2At_spec`
      `xiJetQuot_row0_wp3At_spec`
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Local theorem-level sigma provider from the clean Rec2 true-analytic interface.

This avoids the historical theorem/provider surface
`xiAtOrderSigmaOut_axiom -> xiAtOrderSigmaOut_fromRow0FrontierAtOrder`.
-/
private def xiAtOrderSigmaProvider_fromRec2TrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiAtOrderSigmaProvider where
  sigma := by
    intro m s
    classical
    exact xiAtOrderSigmaOut_fromRec2TrueAnalytic (m := m) (s := s)

/--
Local theorem-level coords provider from clean sigma + Row012 true-analytic.
This is installer-free and used only to freeze the intended clean route into the
historical public theorem surface.
-/
private def xiAtOrderCoords01Provider_fromSigmaAndRow012TrueAnalytic
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic (m := m) (s := s)

/--
Route–B recurrence-natural semantic output.

Public wrapper: call the theorem-level route from `...FromRecurrenceA`, but with:
* clean true-analytic Rec2
* local clean sigma from Rec2
* local clean coords from sigma + Row012 true-analytic
-/
theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  letI : XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by infer_instance
  letI : XiJetQuotRec2AtOrderTrueAnalytic := by infer_instance
  letI : XiAtOrderSigmaProvider :=
    xiAtOrderSigmaProvider_fromRec2TrueAnalytic
  letI : XiSigma3Nonzero := by infer_instance
  letI : XiAtOrderCoords01Provider :=
    xiAtOrderCoords01Provider_fromSigmaAndRow012TrueAnalytic

  exact xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s)

/-- Derived row-0 witness bundle (projection of the full-window contract). -/
noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
