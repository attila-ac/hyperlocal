/-
  Hyperlocal/Targets/XiPacket/XiWindowLemmaC_FromRecurrence.lean

  Plan C++ frontier (shrunk further):

  Instead of axiomatizing the full `XiLemmaC s` (which included κ ≠ 0),
  we axiomatize only the two recurrence consequences

      ell(w0,wc,wp2)=0,  ell(w0,wc,wp3)=0

  plus ONE explicit nonvanishing target at the critical-line anchor:

      (Xi (sc s)).re ≠ 0

  Then κ ≠ 0 is derived purely algebraically from the closed form theorem

      XiLemmaC_kappa_closedForm :
        kappa(reVec3 w0, reVec3 wc, reVec3 ws) = (Xi (sc s)).re
-/

import Hyperlocal.Targets.XiPacket.XiWindowLemmaC
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/--
Smaller semantic output from “recurrence extraction”:

* `hell2/hell3` are the *actual* recurrence-to-window consequences.
* `hRe` is the only remaining nonvanishing semantic target (explicit and recognizable).
-/
structure XiLemmaC_RecOut (s : Hyperlocal.OffSeed Xi) : Prop where
  hell2 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0
  hell3 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0
  hRe :
    (Xi (sc s)).re ≠ 0

/-- Pure algebra: `XiLemmaC_RecOut` already implies the full `XiLemmaC`. -/
theorem XiLemmaC_of_recOut (s : Hyperlocal.OffSeed Xi) (h : XiLemmaC_RecOut s) :
    XiLemmaC s := by
  refine ⟨h.hell2, h.hell3, ?_⟩
  -- Prove κ ≠ 0 by contradiction using the closed form κ = Re(Xi(sc)).
  intro hk0
  have hk :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
        = (Xi (sc s)).re :=
    XiLemmaC_kappa_closedForm (s := s)
  -- From hk0 : kappa = 0 and hk : kappa = Re(Xi), deduce Re(Xi)=0.
  have hXi0 : (Xi (sc s)).re = 0 :=
    hk.symm.trans hk0
  exact h.hRe hXi0

/--
THE (temporary) semantic cliff, now strictly smaller:

recurrence extraction yields the two ell-vanishings plus the explicit `Re(Xi(sc)) ≠ 0`.
-/
axiom xiWindowLemmaC_recOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiLemmaC_RecOut s

/-- Backwards-compatible name: rebuild the full `XiLemmaC` from the smaller RecOut. -/
theorem xiWindowLemmaC_fromRecurrence (s : Hyperlocal.OffSeed Xi) : XiLemmaC s := by
  exact XiLemmaC_of_recOut (s := s) (xiWindowLemmaC_recOut_fromRecurrence (s := s))

end XiPacket
end Targets
end Hyperlocal
