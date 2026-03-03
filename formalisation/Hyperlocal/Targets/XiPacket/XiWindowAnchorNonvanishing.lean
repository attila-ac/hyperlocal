/-
  Hyperlocal/Targets/XiPacket/XiAnchorNonvanishing.lean

  Minimal Prop-class capturing the single anchor nonvanishing obligation used by
  the Toeplitz/κ pipeline.

  This file is intentionally theorem-only: no legacy imports.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Anchor nonvanishing: real part of `Xi` at the seed anchor is nonzero. -/
class XiAnchorNonvanishing (s : Hyperlocal.OffSeed Xi) : Prop :=
  (xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0)

end XiPacket
end Targets
end Hyperlocal
