/-
  Hyperlocal/Targets/XiPacket/XiWindowScNonvanishing.lean

  Cycle-safe semantic endpoint: nonvanishing (in real part) of `Xi` at the
  critical-line anchor point `sc s`.

  NEXT STEP (Task B):
  Replace the axiom `xi_sc_re_ne_zero` by a theorem proved from `XiAnalyticInputs`.
  Downstream should consume `xi_sc_re_ne_zero_of_analytic` (stable name).
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/--
Semantic endpoint (temporary): the real part of `Xi` at the critical-line anchor `sc s` is nonzero.
-/
axiom xi_sc_re_ne_zero (s : OffSeed Xi) : (Xi (sc s)).re ≠ 0

/--
Future-facing theorem name for Task B.

For now, it is just the axiom. Later, replace the body by the real proof and delete the axiom.
-/
theorem xi_sc_re_ne_zero_of_analytic (s : OffSeed Xi) : (Xi (sc s)).re ≠ 0 := by
  simpa using (xi_sc_re_ne_zero (s := s))

end XiPacket
end Targets
end Hyperlocal
