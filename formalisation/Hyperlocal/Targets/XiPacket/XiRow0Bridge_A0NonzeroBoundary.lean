/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_A0NonzeroBoundary.lean

  Minimal boundary: `a0 := JetQuotOp.aRk1 s 0` is nonzero.

  Why this exists:
  Some pure-algebra closed forms for Row012 extra linear constraints divide by `a0`.
  We firewall that denominator as a small, explicit boundary so the rest of the
  route remains cycle-safe.

  IMPORTANT:
  This file is intentionally *small* and may be discharged extractor-side later.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Boundary typeclass: `JetQuotOp.aRk1 s 0 ≠ 0`. -/
class A0Nonzero (s : OffSeed Xi) : Prop where
  a0_ne_zero : JetQuotOp.aRk1 s 0 ≠ 0

/--
Admitted boundary fact (to be discharged later): `a0 ≠ 0`.

If you want to keep this as a *lemma* (not an instance), keep this axiom and
remove the `instance` below; then downstream files can do
`letI : A0Nonzero (s := s) := ⟨a0_ne_zero_boundary (s := s)⟩`.
-/
axiom a0_ne_zero_boundary (s : OffSeed Xi) : JetQuotOp.aRk1 s 0 ≠ 0

/-- Convenience instance so downstream files can just use `infer_instance`. -/
instance (s : OffSeed Xi) : A0Nonzero (s := s) :=
  ⟨a0_ne_zero_boundary (s := s)⟩

end XiPacket
end Targets
end Hyperlocal
