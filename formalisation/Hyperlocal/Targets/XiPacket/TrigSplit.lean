/-
  Hyperlocal/Targets/XiPacket/TrigSplit.lean

  Pure algebra: turn exp(-ρ log p) into the aCoeff/bCoeff cosine-sine split.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/--
Key identity you will use repeatedly:

Re( exp(-(σ+it) log p) * z ) expressed as
aCoeff * Re(z) + bCoeff * Im(z) (or similar), depending on your chosen basis.

You can decide the exact form once you fix whether the window decomposition uses
Re/Im or a rotated basis.
-/
lemma re_mul_exp_neg_rho_log
    (σ t : ℝ) (p : ℝ) (z : ℂ) :
    True := by
  -- TODO: replace `True` by the exact algebraic statement you want,
  -- and prove it using `Complex.exp_mul_I` / `Complex.exp` lemmas.
  trivial

end XiPacket
end Targets
end Hyperlocal
