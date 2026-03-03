/-
  Hyperlocal/Targets/XiPacket/XiWindowAnchorNonvanishingInject.lean

  Legacy provider for `XiAnchorNonvanishing`.

  Policy:
  * This file is the ONLY place that imports the legacy lemma
    `xi_sc_re_ne_zero` from `XiWindowScNonvanishing`.
  * Downstream theorem-level files should depend only on
    `[XiAnchorNonvanishing s]`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing
import Hyperlocal.Targets.XiPacket.XiWindowScNonvanishing  -- legacy seam (localized here)

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Install the minimal anchor nonvanishing gate from the legacy lemma. -/
instance (s : Hyperlocal.OffSeed Xi) : XiAnchorNonvanishing s where
  xi_sc_re_ne_zero := xi_sc_re_ne_zero (s := s)

end XiPacket
end Targets
end Hyperlocal
