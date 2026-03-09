/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProof_Parametric.lean

  Theorem-side sibling surface for the trio AtOrder row-0 spec proofs.

  IMPORTANT:
  * This file is PARAMETRIC.
  * It does NOT install any provider instances.
  * It does NOT replace the historical upstream shim.
  * It exists only to expose the clean theorem body under explicit assumptions.

  Why:
  * `xiJetQuotRec2AtOrder_fromRow012Upstream` still genuinely needs
      [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
  * trying to bypass those assumptions with only
      [XiRow012UpstreamTrueAnalytic]
    causes exactly the synthesis failure you just saw.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiJetQuot_row0_w0At_spec_parametric
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop
  exact Hw.hop_w0At

theorem xiJetQuot_row0_wp2At_spec_parametric
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop
  exact Hw.hop_wp2At

theorem xiJetQuot_row0_wp3At_spec_parametric
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop
  exact Hw.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
