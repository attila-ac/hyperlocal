/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaAt0NonzeroInject.lean

  Temporary provider of `XiKappaAt0Nonzero` from the legacy anchor seam.

  Policy:
  * This is the ONLY place that imports the legacy anchor nonvanishing seam.
  * Downstream algebra/identity files only depend on the class `XiKappaAt0Nonzero`.

  IMPORTANT:
  Do NOT import `XiToeplitzRecurrenceIdentity` here (cycle / dependency inversion).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAt0NonzeroFromScReNonzero
import Hyperlocal.Targets.XiPacket.XiWindowScNonvanishing         -- legacy seam (localized here)

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-!
This file remains the ONLY place that imports the legacy lemma `xi_sc_re_ne_zero`.

We use it solely to provide `[XiScReNonzero s]`.
Then `XiKappaAt0Nonzero s` is obtained theorem-level via
`XiToeplitzRecurrenceKappaAt0NonzeroFromScReNonzero`.
-/

instance (s : Hyperlocal.OffSeed Xi) : XiScReNonzero s := by
  refine ⟨?_⟩
  intro h0
  exact xi_sc_re_ne_zero (s := s) h0

end XiPacket
end Targets
end Hyperlocal
