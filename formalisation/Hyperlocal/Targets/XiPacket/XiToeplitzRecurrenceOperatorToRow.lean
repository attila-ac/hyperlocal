import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperator
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- The real row-vector extracted from the `toeplitzL 2` coefficients (the row giving the dot product). -/
def jetQuotRow3 (s : Hyperlocal.OffSeed Xi) : Fin 3 → ℝ :=
  fun i => Complex.re (JetQuotOp.aRk1 s i)

/--
If the jet-quotient Toeplitz operator annihilates `w` (in the sense that the last coordinate is zero),
then the extracted real row gives a `toeplitzRow3` constraint on `reVec3 w`.
(You can switch to coordinate `0` if your `toeplitzL` convention differs.)
-/
lemma toeplitzRow3_of_jetQuotOp_eq_zero
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h : JetQuotOp.jetQuotToeplitzOp3 s w = 0) :
    toeplitzRow3 (jetQuotRow3 s) (reVec3 w) := by
  classical
  -- expand `jetQuotToeplitzOp3` / `toeplitzL` and take the relevant coordinate,
  -- then take `Complex.re` to get a real dot-product
  -- (implementation depends on which coordinate encodes the row dot product in your Toeplitz convention)
  sorry

end Hyperlocal.Targets.XiPacket
