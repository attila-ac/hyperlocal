/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientManuscriptRow012PropAtOrder.lean

  Manuscript-facing interface (cycle-safe, Prop-level):
  State the AtOrder jet-quotient recurrence in the finite-window Toeplitz form
  (rows 0/1/2 on `Fin 3`) for each of the three AtOrder windows.

  This matches the “exact in the quotient / truncated jet” viewpoint:
  a finite window is a finite object, and the Toeplitz action is evaluated on `Fin 3`.

  This file is defs-only + one axiom placeholder (later replaced by the analytic proof).
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Prop-level row012 contract for a single window. -/
structure ToeplitzRow012Prop (s : OffSeed Xi) (w : Window 3) : Prop where
  h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0
  h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0
  h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0

/--
Prop-level “row012 for all three AtOrder windows”.
This is the manuscript-facing finite-window statement.
-/
structure XiJetQuotRow012PropAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0  : ToeplitzRow012Prop s (w0At m s)
  hwp2 : ToeplitzRow012Prop s (wp2At m s)
  hwp3 : ToeplitzRow012Prop s (wp3At m s)

/--
Convert the Prop-level row012 contract into the Type-level row012 payload
used by the landing pad.
-/
noncomputable def XiJetQuotRow012AtOrder.ofProp
    (m : ℕ) (s : OffSeed Xi) (H : XiJetQuotRow012PropAtOrder m s) :
    XiJetQuotRow012AtOrder m s :=
by
  refine ⟨?h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨H.hw0.h0, H.hwp2.h0, H.hwp3.h0⟩
  · exact H.hw0.h1
  · exact H.hw0.h2
  · exact H.hwp2.h1
  · exact H.hwp2.h2
  · exact H.hwp3.h1
  · exact H.hwp3.h2

/-- Remaining analytic cliff (manuscript-facing, finite-window row012 form). -/
axiom xiJetQuotRow012PropAtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012PropAtOrder m s

end XiPacket
end Targets
end Hyperlocal
