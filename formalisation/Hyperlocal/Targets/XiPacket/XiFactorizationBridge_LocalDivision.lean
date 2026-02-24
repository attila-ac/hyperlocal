/-
  Hyperlocal/Targets/XiPacket/XiFactorizationBridge_LocalDivision.lean

  Minimal bridge: re-export the local-division rigidity lemma from `Hyperlocal.Factorization`
  into the XiPacket namespace layer (so analytic jet files can import *one* thing).
-/

import Hyperlocal.Factorization

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Topology

/-- XiPacket-facing name: local division off the zero set. -/
lemma factorisedByQuartet_eventuallyEq_div
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hfac : Hyperlocal.Factorization.FactorisedByQuartet H ρ k G)
    {z : ℂ} (hz : (Hyperlocal.Factorization.Rρk ρ k).eval z ≠ 0) :
    (∀ᶠ w in 𝓝 z, G w = H w / (Hyperlocal.Factorization.Rρk ρ k).eval w) :=
by
  simpa using
    (Hyperlocal.Factorization.factorisedByQuartet_eventuallyEq_div
      (hfac := hfac) (z := z) hz)

end XiPacket
end Targets
end Hyperlocal
