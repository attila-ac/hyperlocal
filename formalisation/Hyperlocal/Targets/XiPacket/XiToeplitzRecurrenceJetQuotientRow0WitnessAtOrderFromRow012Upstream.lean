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

      ConcreteExtractAtOrderFromRecurrenceB
        -> Row0SemanticsAtOrder
        -> (future sigma import attempt)
        -> ... -> ConcreteExtractAtOrderFromRecurrenceB

  This is a graph-surgery file only; it does not touch shared historical
  provider files.

  Lean 4.23 note:
  `XiJetQuotRow0WitnessCAtOrder m s` is Type-valued, so the exported endpoint
  here must be a `def`, not a `theorem`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream

-- freeze the historical sigma route locally here; this is acyclic because it only
-- depends on the Row0 frontier spec surface, not on the concrete-extract gate.
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Local theorem-level coords provider from sigma + Row012 true-analytic.

Installer-free and used only locally in this upstream row-0 witness file.
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
Local clean recurrence provider, backed by the Row012-upstream theorem route and
the local theorem-level coords provider above.
-/
private def xiJetQuotRec2AtOrderProvider_fromRow012Upstream
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    classical
    letI : XiAtOrderCoords01Provider :=
      xiAtOrderCoords01Provider_fromSigmaAndRow012TrueAnalytic
    exact xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

/--
Type-valued row-0 witness package derived from the Row012-upstream recurrence
route, with only local theorem-backed instance installation.

This is the acyclic replacement dependency for downstream concrete extraction.
-/
noncomputable def xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  letI : XiAtOrderSigmaProvider := by infer_instance
  letI : XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by infer_instance
  letI : XiSigma3Nonzero := by infer_instance
  letI : XiJetQuotRec2AtOrderProvider :=
    xiJetQuotRec2AtOrderProvider_fromRow012Upstream

  exact
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
      (xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
