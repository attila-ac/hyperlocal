/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs.lean

  Pure defs only (cycle breaker):
  * `ToeplitzRow012Prop`
  * `XiJetQuotRow012PropAtOrder`
  * helper `XiJetQuotRow012PropAtOrder.ofProp`

  No imports of any bridge files that depend back on manuscript-facing theorems.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Prop-level row012 Toeplitz equalities for a Window-3 vector `w`. -/
structure ToeplitzRow012Prop (s : OffSeed Xi) (w : Window 3) : Prop where
  h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0
  h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0
  h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0

/--
Prop-level manuscript endpoint (AtOrder):
row012 Toeplitz equalities for `w0At/wp2At/wp3At`.
-/
abbrev XiJetQuotRow012PropAtOrder (m : ℕ) (s : OffSeed Xi) : Prop :=
  ToeplitzRow012Prop s (w0At m s) ∧
  ToeplitzRow012Prop s (wp2At m s) ∧
  ToeplitzRow012Prop s (wp3At m s)

namespace XiJetQuotRow012PropAtOrder

/-- Constructor helper: bundle the three Prop-level row012 payloads. -/
theorem ofProp (m : ℕ) (s : OffSeed Xi)
    (hw0  : ToeplitzRow012Prop s (w0At m s))
    (hwp2 : ToeplitzRow012Prop s (wp2At m s))
    (hwp3 : ToeplitzRow012Prop s (wp3At m s)) :
    XiJetQuotRow012PropAtOrder m s :=
  ⟨hw0, ⟨hwp2, hwp3⟩⟩

end XiJetQuotRow012PropAtOrder

end XiPacket
end Targets
end Hyperlocal
