/-
  XiWindowScNonvanishing.lean

  DEPRECATED LEGACY ENDPOINT.

  This file is retained only for older branches that still expect theorem names
  `xi_sc_re_ne_zero` / `xi_sc_re_ne_zero_of_analytic`.

  UPDATED POLICY:
  * this file contains no axioms
  * the old names are theorem-backed wrappers around `XiAnchorNonvanishing`

  The W1 / Plan C++J pipeline MUST NOT depend on this file directly.
  Use `XiWindowAnchorNonvanishing` and theorem-side payload constructors instead.
-/

import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Legacy semantic endpoint, now theorem-backed from `XiAnchorNonvanishing`. -/
theorem xi_sc_re_ne_zero (s : OffSeed Xi) [XiAnchorNonvanishing s] :
    (Xi (sc s)).re ≠ 0 :=
  XiAnchorNonvanishing.xi_sc_re_ne_zero (s := s)

/-- Legacy “future-facing” name; now just a theorem alias. -/
theorem xi_sc_re_ne_zero_of_analytic (s : OffSeed Xi) [XiAnchorNonvanishing s] :
    (Xi (sc s)).re ≠ 0 := by
  simpa using (xi_sc_re_ne_zero (s := s))

end XiPacket
end Targets
end Hyperlocal
