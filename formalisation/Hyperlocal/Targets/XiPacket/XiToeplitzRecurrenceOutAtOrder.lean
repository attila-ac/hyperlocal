/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceOutAtOrder.lean

  “AtOrder” variant of the Toeplitz/recurrence extraction contracts.

  This mirrors `XiToeplitzRecurrenceOut.lean`, but replaces the base central
  window `w0` and the prime windows `wp2/wp3` by their jet-pivot counterparts
  at order `m`:

    w0At m s,  wp2At m s,  wp3At m s.

  The intent is to allow the Option-ELL path to use κ-nonvanishing witnesses
  coming from jet-nonflatness at some order, without assuming any value-level
  anchor nonvanishing at order 0.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/-- Span-output at order `m`: the prime windows lie in the ℝ-span of `{w0At m, wc}`. -/
structure XiToeplitzSpanOutAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop where
  hspan2 : ∃ (α β : ℝ),
    reVec3 (wp2At m s) = α • reVec3 (w0At m s) + β • reVec3 (wc s)
  hspan3 : ∃ (α β : ℝ),
    reVec3 (wp3At m s) = α • reVec3 (w0At m s) + β • reVec3 (wc s)

/-- Ell-output at order `m`: the two determinant vanishings. -/
structure XiToeplitzEllOutAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop where
  hell2 :
    Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0
  hell3 :
    Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0

namespace XiToeplitzEllOutAt
end XiToeplitzEllOutAt

end XiPacket
end Targets
end Hyperlocal
