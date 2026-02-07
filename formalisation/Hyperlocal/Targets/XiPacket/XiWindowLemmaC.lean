/-
  Hyperlocal/Targets/XiPacket/XiWindowLemmaC.lean

  Phase 4.5 (Plan C++):
  Isolate the *entire* remaining ξ-semantic cliff as a single Prop bundle:

    XiLemmaC s : Prop

  providing exactly the three facts needed by `xiWindowPayload_of_C`:
    • ell(..., wp2) = 0
    • ell(..., wp3) = 0
    • kappa(..., ws) ≠ 0

  Everything downstream should depend only on `XiLemmaC`, not on how it is proved.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowPayloadConstructor
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- The entire “Lemma C” semantic package, stated purely about definitional ξ-windows. -/
structure XiLemmaC (s : Hyperlocal.OffSeed Xi) : Prop where
  hell2 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0
  hell3 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0
  hkappa :
    Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0

/--
Canonical Phase-4.5 constructor:
once you have `XiLemmaC s`, you get the full `WindowPayload` for free.
-/
def xiWindowPayload (s : Hyperlocal.OffSeed Xi) (hC : XiLemmaC s) :
    WindowPayload s.ρ.re s.ρ.im :=
  xiWindowPayload_of_C (s := s) hC.hell2 hC.hell3 hC.hkappa

end XiPacket
end Targets
end Hyperlocal
