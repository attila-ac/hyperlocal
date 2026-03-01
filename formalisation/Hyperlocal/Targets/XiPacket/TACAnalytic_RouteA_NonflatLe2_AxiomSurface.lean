/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_RouteA_NonflatLe2_AxiomSurface.lean

  Front~NF (Route–A nonflatness) — **DISCHARGED surface**.

  REFACTOR (2026-03-01):
  This file used to be the temporary axiom surface for Route–A bounded nonflatness
  at the four canonical anchors.  The proofs are now provided in

    `TACAnalytic_RouteA_NonflatLe2_Landing.lean`

  and this file is kept as a stable “front door” for downstream imports,
  so *all consumers remain unchanged* while the internal proof strategy evolves.

  Policy:
  - Downstream should import THIS file, never the landing file directly.
  - This file must remain extractor-free.
-/

import Hyperlocal.Targets.XiPacket.TACAnalytic_RouteA_NonflatLe2_Landing

-- Re-export the four anchor lemmas under the same names / namespace.
-- (They are already stated as theorems in the landing file, so no new declarations are needed.)

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace TAC

-- Theorems available from the landing import:
--   routeA_G_nonflat_le2_at_rho_iterated
--   routeA_G_nonflat_le2_at_conj_rho_iterated
--   routeA_G_nonflat_le2_at_one_sub_conj_rho_iterated
--   routeA_G_nonflat_le2_at_one_sub_rho_iterated

end TAC

end XiPacket
end Targets
end Hyperlocal
