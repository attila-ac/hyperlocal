/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizAtFromRouteA.lean

  Route-A: provide JetLeibnizAt for the four canonical windows.

  Cycle safety:
  * This file must not import any Row0Semantics / Row0ConcreteProof modules.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

/-
We use `z := s.ρ` (field of OffSeed) instead of a separate `rho` identifier.
If you *do* have a `rho : OffSeed Xi → ℂ` elsewhere, keeping `s.ρ` here is still safe.
-/

/-- Route-A input package: enough data to discharge `JetLeibnizAt` at a given window. -/
axiom xiRouteA_jetPkg (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
  ∃ G : ℂ → ℂ,
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    Differentiable ℂ (Rfun s) ∧
    Differentiable ℂ G ∧
    Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
    Differentiable ℂ (fun t => deriv G t)

/-- `JetLeibnizAt` for the central window `w0` at `z = s.ρ`. -/
theorem xiJetLeibnizAt_w0 (s : OffSeed Xi) :
  JetLeibnizAt s (s.ρ) (w0 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := s.ρ) (w := w0 s)
    (xiRouteA_jetPkg (s := s) (z := s.ρ) (w := w0 s))

/-- `JetLeibnizAt` for the conjugate window `wc` at `z = 1 - s.ρ`. -/
theorem xiJetLeibnizAt_wc (s : OffSeed Xi) :
  JetLeibnizAt s (1 - s.ρ) (wc s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - s.ρ) (w := wc s)
    (xiRouteA_jetPkg (s := s) (z := 1 - s.ρ) (w := wc s))

/-- `JetLeibnizAt` for `wp2` at `z = star(s.ρ)` (as `starRingEnd`). -/
theorem xiJetLeibnizAt_wp2 (s : OffSeed Xi) :
  JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (xiRouteA_jetPkg (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s))

/-- `JetLeibnizAt` for `wp3` at `z = 1 - star(s.ρ)` (as `starRingEnd`). -/
theorem xiJetLeibnizAt_wp3 (s : OffSeed Xi) :
  JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3 s)
    (xiRouteA_jetPkg (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3 s))


end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
