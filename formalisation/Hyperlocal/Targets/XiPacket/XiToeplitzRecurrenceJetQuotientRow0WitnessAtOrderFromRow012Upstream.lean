/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream.lean

  Theorem-level row-0 witness at order, sourced from the Row012-upstream
  recurrence route with only local theorem-backed instance installation.

  Purpose:
  * provide `XiJetQuotRow0WitnessCAtOrder m s` upstream of the historical
    public semantics wrapper
  * let downstream concrete extraction consume the row-0 witness directly
    without importing
      `XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean`
  * break the cycle

  BREAKTHROUGH ATTEMPT:
  this file now bypasses `XiJetQuotRec2AtOrderProvider` completely and feeds an
  explicit clean recurrence payload into `xiJetQuotOpZeroAtOrder_of_rec2`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

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
Local clean sigma provider sourced from the Rec2 true-analytic theorem route.
-/
private def xiAtOrderSigmaProvider_fromRec2TrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_fromRec2TrueAnalytic

/--
Local theorem-level coords provider from clean sigma + Row012 true-analytic.
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
Type-valued row-0 witness package derived from the Row012-upstream recurrence
route, with only local theorem-backed instance installation.
-/
noncomputable def xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  letI : XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by infer_instance
  letI : XiJetQuotRec2AtOrderTrueAnalytic := by infer_instance
  letI : XiAtOrderSigmaProvider :=
    xiAtOrderSigmaProvider_fromRec2TrueAnalytic
  letI : XiSigma3Nonzero := by infer_instance
  letI : XiAtOrderCoords01Provider :=
    xiAtOrderCoords01Provider_fromSigmaAndRow012TrueAnalytic

  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  exact
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
      (xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec)

end XiPacket
end Targets
end Hyperlocal
