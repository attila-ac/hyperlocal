/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom.lean

  Analytic (non-cycle-safe) landing axiom for the Row012 target bundle.

  IMPORTANT:
  This MUST remain primitive (axiom or later true analytic proof) because the extractor
  stack depends on it, and the Route–C proof stack now depends (indirectly) on the extractor
  via the heart discharge.

  If you try to define this from Route–C, you create an import cycle.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-
Upstream analytic endpoint: provide the Type-valued Row012 target bundle.

This file is the *unique extractor-facing import*.
Its implementation is delegated to `...AnalyticProofUpstream` to keep the dependency DAG cycle-free.
-/
noncomputable def xiJetQuotRow012AtOrder_analytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
