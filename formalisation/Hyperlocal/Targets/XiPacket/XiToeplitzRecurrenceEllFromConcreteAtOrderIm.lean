/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrderIm.lean

  Imag-pivot analogue of `XiToeplitzRecurrenceEllFromConcreteAtOrder`.

  IMPORTANT (current status):
  This file is a **semantic cliff / placeholder**. The concrete Toeplitz-row-0
  transport route for the imag-pivot columns is still being stabilized.

  Downstream consumers (notably `XiToeplitzRecurrenceIdentityIm`) only need the
  ell-out statements at order `m`.

  Once the JetQuot/row0 witness surface is reinstated on the theorem route,
  these axioms should be replaced by the corresponding proofs.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Ell-out at order `m` for the imag-pivot columns:
`u0 = imVec3(w0At m s)`, `uc = reVec3(wc s)`,
and `up = imVec3(wp2At/wp3At m s)`.

(Placeholder axiom; theorem route to be restored.)
-/
axiom xiToeplitzEllOutAtIm_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp3At m s)) = 0

/--
Ell-out at order `m` for the *mixed* imag-pivot configuration used by the pivot-gate
consumer:

`u0 = imVec3(w0At m s)`, `uc = reVec3(wc s)`, and `up = reVec3(wp2At/wp3At m s)`.

(Placeholder axiom; theorem route to be restored.)
-/
axiom xiToeplitzEllOutAtImRe_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0

/--
Auxiliary ell-out at order `m` for the mixed configuration with `up = reVec3(w0At m s)`.
Used by the imag-pivot identity consumer to cancel the `reVec3(w0At)` contribution.

(Placeholder axiom; theorem route to be restored.)
-/
axiom xiToeplitzEllOutAtImRe_w0_fromRecurrenceC (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s)) = 0

end XiPacket
end Targets
end Hyperlocal
