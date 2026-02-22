/-
  Hyperlocal/Targets/XiPacket/XiJet3AtOrderDefs.lean

  Canonical length-3 jet window at order m:
    jet3 of the function (cderivIter m Xi) at z.

  NOTE:
  We intentionally define entries 1 and 2 using `deriv` at `z`, to avoid needing
  the commutation lemma `deriv (deriv^[m] Xi) = deriv^[m] (deriv Xi)` in this snapshot.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Order-`m` length-3 derivative jet window of `Xi` at `z`,
defined as the Jet3 window of the function `cderivIter m Xi` at `z`. -/
def xiJet3AtOrder (m : ℕ) (z : ℂ) : Transport.Window 3 :=
  ![ cderivIter m Xi z
   , deriv (cderivIter m Xi) z
   , deriv (deriv (cderivIter m Xi)) z ]

/-- Tautological Jet3 predicate for the order-`m` jet: Jet3 of `cderivIter m Xi`. -/
def IsJet3AtOrder (m : ℕ) (z : ℂ) (w : Transport.Window 3) : Prop :=
  IsJet3At (cderivIter m Xi) z w

@[simp] theorem isJet3AtOrder_xiJet3AtOrder (m : ℕ) (z : ℂ) :
    IsJet3AtOrder m z (xiJet3AtOrder m z) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · change (xiJet3AtOrder m z (0 : Fin 3)) = (cderivIter m Xi) z
    simp [xiJet3AtOrder]
  · change (xiJet3AtOrder m z (1 : Fin 3)) = deriv (cderivIter m Xi) z
    simp [xiJet3AtOrder]
  · change (xiJet3AtOrder m z (2 : Fin 3)) = deriv (deriv (cderivIter m Xi)) z
    simp [xiJet3AtOrder]

end XiPacket
end Targets
end Hyperlocal
