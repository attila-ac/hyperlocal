/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA.lean

  Bridge layer to *reduce* the Route-A jet-package axiom surface.

  Context:
  * We already have a theorem-level analytic construction of a quartet quotient `G`
    (via `G_Xi_entire` in `XiAnalyticInputs`) and a theorem-level discharge of
    `JetLeibnizAt` for the *canonical* raw jet window `jet3 G z`.
  * What is still missing to remove the old axiom
      `JetQuotOp.xiRouteA_jetPkg (s) (z) (w)`
    is a proof that the concrete ξ-windows used downstream (`w0/wc/wp2/wp3`, and
    the jet-pivot variants `w0At/wp2At/wp3At`) are *equal* to those canonical
    jet windows of the quotient.

  This file isolates that missing content as *small, explicit axioms* for the
  specific windows actually used by Route-A consumers.

  Later, these axioms should be replaced by genuine theorems derived from:
    - the definition of the ξ-windows (Plan C++ and C++J),
    - the quotient definition `G = Xi / Rfun s` (or your factorisation API),
    - transport/shift lemmas for `XiTransportOp`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

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

/-!
  ### The remaining Route-A bridge obligations (currently axiomatic)

  These say that the concrete ξ-windows are the canonical jet windows of the
  chosen quotient `routeA_G s` at the relevant centers.

  Once these are theorem-level, the old axiom `xiRouteA_jetPkg` can be deleted.
-/

axiom w0_eq_jet3_routeA (s : OffSeed Xi) :
    w0 s = jet3 (routeA_G s) (s.ρ)

axiom wc_eq_jet3_routeA (s : OffSeed Xi) :
    wc s = jet3 (routeA_G s) (1 - s.ρ)

axiom wp2_eq_jet3_routeA (s : OffSeed Xi) :
    wp2 s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)

axiom wp3_eq_jet3_routeA (s : OffSeed Xi) :
    wp3 s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)

/-!
  Jet-pivot windows (Plan C++J).

  These are the ones used by the Row012/Rec2 extraction chain.
  They are indexed by the jet-pivot order `m` and are still (currently)
  provided by axioms.
-/

axiom w0At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    w0At m s = jet3 (routeA_G s) (s.ρ)

axiom wp2At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)

axiom wp3At_eq_jet3_routeA (m : ℕ) (s : OffSeed Xi) :
    wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)

end XiPacket
end Targets
end Hyperlocal
