/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom.lean

  Analytic landing for the Row012 target bundle.

  IMPORTANT (new graph discipline):
  * this file is now interface-parametric
  * it must NOT import provider installers
  * it must NOT import historical theorem/axiom installer surfaces

  Reason:
  The analytic extractor is the only downstream consumer of this file.
  If this file imports installed sigma/coords providers directly, it freezes those
  historical surfaces into the extractor cone and can create import cycles.

  The installed extractor-facing import surface now lives in the separate file:

    XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstaller.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream

-- provider interfaces only
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-
Parametric analytic endpoint: provide the Type-valued Row012 target bundle.

This file is now upstream/interface-only.
Concrete provider installation is delegated to the separate installer import surface.
-/
noncomputable def xiJetQuotRow012AtOrder_analytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
