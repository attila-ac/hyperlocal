/-
  Hyperlocal/Targets/XiPacket/XiRouteA_GDefs.lean

  Axiom-free definitions for the Route-A quotient witness `routeA_G s`
  extracted from `G_Xi_entire s`, together with its factorisation and
  entire-ness proofs.

  IMPORTANT:
  * This file intentionally contains NO window=jet axioms.
  * It depends only on the Route-A analytic input shims.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs_Factorization

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- A fixed choice of Route-A quotient `G` from `G_Xi_entire`. -/
noncomputable def routeA_G (s : OffSeed Xi) : ℂ → ℂ :=
  Classical.choose (G_Xi_entire s)

lemma routeA_G_factorised (s : OffSeed Xi) :
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 (routeA_G s) :=
  (Classical.choose_spec (G_Xi_entire s)).1

lemma routeA_G_entire (s : OffSeed Xi) :
    Hyperlocal.GrowthOrder.EntireFun (routeA_G s) :=
  (Classical.choose_spec (G_Xi_entire s)).2

end XiPacket
end Targets
end Hyperlocal
