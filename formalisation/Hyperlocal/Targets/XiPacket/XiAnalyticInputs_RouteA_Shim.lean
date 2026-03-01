import Hyperlocal.Targets.XiPacket.XiAnalyticInputs_FE_FromMathlib
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs_Entire_FromMathlib
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs_RC_FromMathlib
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs_FactorisationHandoff_RouteA
-- ^ rename this import to whatever file currently contains Xi_exists_factorisedByQuartet_entire,
--   Rquartet, R_quartet_zeros, G_Xi_entire (the green file you pasted)

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-!
# Analytic Inputs for Xi (Route A) — Shim

This file is intentionally tiny:
it only *imports* the Mathlib bridges (FE / Entire / RC) and the Route-A
factorisation handoff, and then re-exports the public-facing theorems/defs.

Downstream Route-A files should import THIS shim, not the individual bridges.
-/

-- Keep the local name stable for downstream code.
private abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- FE: `Xi (1 - s) = Xi s`. -/
theorem Xi_FE' : Hyperlocal.Factorization.FunFE Xi :=
  Xi_FE

/-- Entirety: `Xi` is analytic everywhere (as used by GrowthOrder). -/
theorem Xi_entire' : Hyperlocal.GrowthOrder.EntireFun Xi :=
  Xi_entire

/-- RC: `Xi (conj s) = conj (Xi s)`. -/
theorem Xi_RC' : Hyperlocal.FactorizationRC.FunRC Xi :=
  Xi_RC

/-! Re-export the quartet polynomial & zeros package (Route A). -/

-- If your factorisation handoff file already defines these in the same namespace,
-- you can `export` them instead of re-declaring.
-- Example:
-- export Hyperlocal.Targets.XiPacket (Rquartet R_quartet_zeros G_Xi_entire)

end XiPacket
end Targets
end Hyperlocal
