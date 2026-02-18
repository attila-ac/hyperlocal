/-
  Hyperlocal/Targets/XiPacket/XiWindowScNonvanishing.lean

  Cycle-safe semantic endpoint: nonvanishing (in real part) of `Xi` at the
  critical-line anchor point `sc s`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/--
Semantic endpoint: the real part of `Xi` at the critical-line anchor `sc s` is nonzero.
-/
axiom xi_sc_re_ne_zero (s : OffSeed Xi) : (Xi (sc s)).re ≠ 0

end XiPacket
end Targets
end Hyperlocal
