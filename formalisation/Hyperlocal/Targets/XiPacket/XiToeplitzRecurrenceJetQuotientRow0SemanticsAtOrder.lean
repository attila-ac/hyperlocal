/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  AtOrder Route–B semantics (public surface).

  Definitions are in:
    XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs.lean

  Provider refactor (2026-02-22):
  `xiJetQuotOpZeroAtOrder_fromRecurrenceA` consumes the recurrence payload via
  a typeclass `[XiJetQuotRec2AtOrderProvider]`.

  CLEAN SIGMA/COORDS/REC2 RETARGET:
  The public wrapper now freezes the full clean theorem-production spine locally:

    Row012 true-analytic
      -> clean sigma from Rec2 true-analytic
      -> clean coords01 from explicit sigma + Row012 true-analytic
      -> explicit local Rec2 provider from Row012 upstream
      -> `xiJetQuotOpZeroAtOrder_fromRecurrenceA`

  Goal:
  avoid any fallback through global provider selection at the public wrapper site.
-/
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

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
-/
private def xiAtOrderSigmaProvider_fromRec2TrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiAtOrderSigmaProvider where
  sigma := by
    intro m s
    classical
    exact xiAtOrderSigmaOut_fromRec2TrueAnalytic (m := m) (s := s)

/--
Local theorem-level coords provider from explicit sigma + Row012 true-analytic.
This uses the explicit-input theorem, not the provider-facing wrapper.
-/
private def xiAtOrderCoords01Provider_ofSigmaAndRow012TrueAnalytic
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    have Hσ : XiAtOrderSigmaOut m s :=
      xiAtOrderSigmaOut_provided (m := m) (s := s)
    exact xiAtOrderCoords01Out_of_sigmaAndRow012TrueAnalytic
      (m := m) (s := s) Hσ

/--
Local clean recurrence provider, backed explicitly by the Row012-upstream theorem
route and the locally frozen clean sigma/coords providers above.
-/
private def xiJetQuotRec2AtOrderProvider_fromRow012Upstream
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    classical
    exact xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

/--
Route–B recurrence-natural semantic output.

Public wrapper: call the theorem-level route from `...FromRecurrenceA`, but with:
* clean true-analytic Rec2 interface
* local clean sigma from Rec2
* local clean coords from explicit sigma + Row012 true-analytic
* explicit local clean Rec2 provider from Row012 upstream
-/
theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  letI : XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by infer_instance
  letI : XiJetQuotRec2AtOrderTrueAnalytic := by infer_instance
  letI : XiAtOrderSigmaProvider :=
    xiAtOrderSigmaProvider_fromRec2TrueAnalytic
  letI : XiSigma3Nonzero := by infer_instance
  letI : XiAtOrderCoords01Provider :=
    xiAtOrderCoords01Provider_ofSigmaAndRow012TrueAnalytic
  letI : XiJetQuotRec2AtOrderProvider :=
    xiJetQuotRec2AtOrderProvider_fromRow012Upstream

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
