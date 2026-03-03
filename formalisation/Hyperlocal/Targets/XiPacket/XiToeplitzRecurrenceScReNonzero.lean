/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceScReNonzero.lean

  Minimal Prop-class gate for the anchor nonvanishing seam needed by the κ/Toeplitz route.

  Policy:
  * This file is theorem-only: it does NOT import any legacy seam/axiom.
  * Downstream files should depend only on `[XiScReNonzero s]`.
  * A separate injector may provide instances temporarily.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Gate: real part of `Xi` at the anchor `sc s` is nonzero. -/
class XiScReNonzero (s : Hyperlocal.OffSeed Xi) : Prop where
  out : (Xi (sc s)).re ≠ 0

/-- Convenience lemma for rewriting. -/
@[simp] lemma xi_sc_re_ne_zero_of_inst (s : Hyperlocal.OffSeed Xi) [h : XiScReNonzero s] :
    (Xi (sc s)).re ≠ 0 :=
  h.out

end XiPacket
end Targets
end Hyperlocal
