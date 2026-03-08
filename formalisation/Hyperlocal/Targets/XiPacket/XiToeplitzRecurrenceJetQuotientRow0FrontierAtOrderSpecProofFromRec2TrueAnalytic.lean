import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

private def xiAtOrderSigmaProvider_fromRec2TrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiAtOrderSigmaProvider where
  sigma := by
    intro m s
    classical
    exact xiAtOrderSigmaOut_fromRec2TrueAnalytic (m := m) (s := s)

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

private def xiJetQuotRec2AtOrderProvider_fromRow012Upstream
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    classical
    exact xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

private theorem xiJetQuotOpZeroAtOrder_clean
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
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

theorem xiJetQuot_row0_w0At_spec_proof
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 := by
  classical
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_clean (m := m) (s := s)
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop
  simpa using Hw.hop_w0At

theorem xiJetQuot_row0_wp2At_spec_proof
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 := by
  classical
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_clean (m := m) (s := s)
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop
  simpa using Hw.hop_wp2At

theorem xiJetQuot_row0_wp3At_spec_proof
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 := by
  classical
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_clean (m := m) (s := s)
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop
  simpa using Hw.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
