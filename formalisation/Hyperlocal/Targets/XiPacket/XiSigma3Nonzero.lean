/-
  Hyperlocal/Targets/XiPacket/XiSigma3Nonzero.lean

  Minimal nondegeneracy interface: σ3(s) ≠ 0.

  This file provides a default instance from the existing boundary
    `A0Nonzero (s := s)` giving `JetQuotOp.aRk1 s 0 ≠ 0`.
  Since `aRk1 s 0 = aR s 1 = -σ3 s`, we get `σ3 s ≠ 0`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Minimal nondegeneracy interface for Tail345 coordinate kill: `σ3(s) ≠ 0`. -/
class XiSigma3Nonzero : Prop where
  sigma3_ne_zero : ∀ (s : OffSeed Xi), (JetQuotOp.σ3 s : ℂ) ≠ 0

/--
Default bridge:
from `A0Nonzero (s := s)` we have `aRk1 s 0 ≠ 0`,
and `aRk1 s 0 = -σ3 s`, hence `σ3 s ≠ 0`.
-/
instance (priority := 900) : XiSigma3Nonzero := by
  refine ⟨?_⟩
  intro s
  -- pull the boundary fact from the typeclass
  have h : JetQuotOp.aRk1 s 0 ≠ (0 : ℂ) := (A0Nonzero.a0_ne_zero (s := s))
  -- rewrite `aRk1 s 0` as `-σ3 s`
  have hneg : (-(JetQuotOp.σ3 s : ℂ)) ≠ 0 := by
    simpa [JetQuotOp.aRk1, JetQuotOp.aR] using h
  exact neg_ne_zero.mp hneg

end XiPacket
end Targets
end Hyperlocal
