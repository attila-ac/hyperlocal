/-
  Hyperlocal/Targets/XiPacket/XiLemmaA_ToeplitzTransport.lean

  Phase 3A: Lemma A (Toeplitz/transport audit) for definitional ξ-windows.

  By design (your XiTransportOp is defined Toeplitz/shift-generated),
  Lemma A is audit-level: it just exposes the definitional equalities.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/-- `w0` is definitional: it is exactly the transported central jet. -/
theorem XiLemmaA_w0_def (s : _root_.Hyperlocal.OffSeed Xi) :
    w0 s = xiTransportedJet s := by
  rfl

/-- `xiTransportedJet` is definitional: it is `XiTransportOp` applied to the central jet. -/
theorem XiLemmaA_xiTransportedJet_def (s : _root_.Hyperlocal.OffSeed Xi) :
    xiTransportedJet s =
      (_root_.Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (xiCentralJet s) := by
  rfl

/-- Combined audit form: `w0` is the `XiTransportOp`-transported jet. -/
theorem XiLemmaA_w0_as_XiTransportOp (s : _root_.Hyperlocal.OffSeed Xi) :
    w0 s =
      (_root_.Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (xiCentralJet s) := by
  rfl

end XiPacket
end Targets
end Hyperlocal
