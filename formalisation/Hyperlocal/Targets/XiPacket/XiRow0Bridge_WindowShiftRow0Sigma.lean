/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WindowShiftRow0Sigma.lean

  Shift lemmas for Window-3 objects and the Row-0 scalar form `row0Sigma`.

  This file is purely algebraic and cycle-safe:
  it uses `shiftLₗ 2` coordinate computations and unfolds `row0Sigma`.

  The key outputs:
    row0Sigma s (shiftLₗ 2 w)  =  σ2*s*w2  + (-σ3*s)*w1
    row0Sigma s (shiftLₗ 2 (shiftLₗ 2 w)) = (-σ3*s)*w2

  These are the exact "row1 / row2" forms (up to your coefficient conventions).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open ToeplitzLToRow3

/-- One-step left shift of a Window-3 (implemented as `shiftLₗ 2`). -/
abbrev shiftWin1 (w : Window 3) : Window 3 := shiftLₗ 2 w

/-- Two-step left shift of a Window-3. -/
abbrev shiftWin2 (w : Window 3) : Window 3 := shiftLₗ 2 (shiftLₗ 2 w)

/--
Compute `row0Sigma` on the one-step shift.

Since `shiftWin1 w` has coordinates `(w1, w2, 0)`, we get:
  row0Sigma s (shiftWin1 w) = σ2*s*w2 + (-σ3*s)*w1.
-/
theorem row0Sigma_shiftWin1
    (s : OffSeed Xi) (w : Window 3) :
    row0Sigma s (shiftWin1 w)
      = (JetQuotOp.σ2 s) * (w (2 : Fin 3)) + (-JetQuotOp.σ3 s) * (w (1 : Fin 3)) := by
  classical
  -- unfold shiftWin1 and row0Sigma; then use the coordinate lemmas for `shiftLₗ 2`
  simp [shiftWin1, row0Sigma,
        toeplitzL_two_apply_fin0,  -- not strictly needed but harmless if row0Sigma expands through it
        shiftLₗ_two_apply0, shiftLₗ_two_apply1, shiftLₗ_two_apply2,
        add_assoc, add_left_comm, add_comm, mul_assoc, mul_add]

/--
Compute `row0Sigma` on the two-step shift.

Since `shiftWin2 w` has coordinates `(w2, 0, 0)`, we get:
  row0Sigma s (shiftWin2 w) = (-σ3*s)*w2.
-/
theorem row0Sigma_shiftWin2
    (s : OffSeed Xi) (w : Window 3) :
    row0Sigma s (shiftWin2 w)
      = (-JetQuotOp.σ3 s) * (w (2 : Fin 3)) := by
  classical
  simp [shiftWin2, shiftWin1, row0Sigma,
        shiftLₗ_two_apply0, shiftLₗ_two_apply1, shiftLₗ_two_apply2,
        add_assoc, add_left_comm, add_comm, mul_assoc, mul_add]

namespace WindowShiftRow0SigmaExport
export _root_.Hyperlocal.Targets.XiPacket
  (shiftWin1 shiftWin2 row0Sigma_shiftWin1 row0Sigma_shiftWin2)
end WindowShiftRow0SigmaExport

end XiPacket
end Targets
end Hyperlocal
