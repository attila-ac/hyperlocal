/-
  Hyperlocal/Targets/XiPacket/XiJet3AtOrderQuotDefs.lean

  Order-m Jet3 predicate, but for the Route-A quotient model `routeA_G s`.

  IMPORTANT:
  The existing Route-A bridge axioms identify the concrete windows
  `w0At/wp2At/wp3At` with `jet3 (routeA_G s)` at the centers, not with
  `jet3 (cderivIter m (routeA_G s))`. Therefore this definition *keeps* the `m`
  parameter for API compatibility but does not use it.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Order-`m` length-3 jet predicate for the Route-A quotient `routeA_G s` at `z`.
The parameter `m` is retained for downstream API compatibility. -/
def IsJet3AtOrderQuot (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3) : Prop :=
  IsJet3At (routeA_G s) z w

/--
Unindexed (hygienic) Route-A quotient jet predicate.

This is the semantic core of `IsJet3AtOrderQuot`; keeping it separate avoids the
illusion that `m` plays a role for quotient jets.
-/
def IsJet3AtQuot (s : OffSeed Xi) (z : ℂ) (w : Window 3) : Prop :=
  IsJet3At (routeA_G s) z w

@[simp] lemma isJet3AtOrderQuot_eq (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3) :
    IsJet3AtOrderQuot m s z w = IsJet3AtQuot s z w := rfl

@[simp] lemma isJet3AtOrderQuot_iff (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3) :
    IsJet3AtOrderQuot m s z w ↔ IsJet3AtQuot s z w := Iff.rfl

end XiPacket
end Targets
end Hyperlocal
