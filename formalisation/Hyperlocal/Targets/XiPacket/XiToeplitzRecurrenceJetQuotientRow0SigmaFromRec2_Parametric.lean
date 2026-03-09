import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem row0Sigma_w0_eq_zero_fromRec2_parametric
    (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    row0Sigma s (w0 s) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder 0 s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := 0) (s := s)
  have Hop : XiJetQuotOpZeroAtOrder 0 s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := 0) (s := s) Hrec
  have Hw : XiJetQuotRow0WitnessCAtOrder 0 s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := 0) (s := s) Hop
  simpa [toeplitzL_row0_eq_row0Sigma] using Hw.hop_w0At

theorem row0Sigma_wp2_eq_zero_fromRec2_parametric
    (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    row0Sigma s (wp2 s) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder 0 s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := 0) (s := s)
  have Hop : XiJetQuotOpZeroAtOrder 0 s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := 0) (s := s) Hrec
  have Hw : XiJetQuotRow0WitnessCAtOrder 0 s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := 0) (s := s) Hop
  simpa [toeplitzL_row0_eq_row0Sigma] using Hw.hop_wp2At

theorem row0Sigma_wp3_eq_zero_fromRec2_parametric
    (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    row0Sigma s (wp3 s) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder 0 s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := 0) (s := s)
  have Hop : XiJetQuotOpZeroAtOrder 0 s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := 0) (s := s) Hrec
  have Hw : XiJetQuotRow0WitnessCAtOrder 0 s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := 0) (s := s) Hop
  simpa [toeplitzL_row0_eq_row0Sigma] using Hw.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
