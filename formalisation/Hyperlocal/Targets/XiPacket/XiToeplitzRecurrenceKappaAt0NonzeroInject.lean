/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaAt0NonzeroInject.lean

  Temporary provider of `XiKappaAt0Nonzero` from the legacy anchor seam.

  Policy:
  * This is the ONLY place that imports the legacy anchor nonvanishing seam.
  * Downstream algebra/identity files only depend on the class `XiKappaAt0Nonzero`.

  IMPORTANT:
  Do NOT import `XiToeplitzRecurrenceIdentity` here (cycle / dependency inversion).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAt0Nonzero
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowScNonvanishing         -- legacy seam (localized here)
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder  -- κ closed form at order m

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Helper: κ≠0 at order 0 from closed form + `xi_sc_re_ne_zero`. -/
theorem xi_kappaAt0_ne0_from_anchorSeam (s : Hyperlocal.OffSeed Xi) : kappaAt0 s ≠ 0 := by
  intro hk0
  -- κ closed form at order 0: κ = Re (cderivIter 0 Xi (sc s))
  have hk :
      kappaAt0 s = (((cderivIter (0 : ℕ) Xi) (sc s))).re := by
    simpa [kappaAt0] using (XiLemmaC_kappa_closedFormAt (m := (0 : ℕ)) (s := s))

  have hRe0 : (((cderivIter (0 : ℕ) Xi) (sc s))).re = 0 :=
    hk.symm.trans hk0

  have : (Xi (sc s)).re = 0 := by
    simpa [cderivIter] using hRe0

  exact xi_sc_re_ne_zero (s := s) this

/-- Install the minimal κ≠0 gate needed by the Toeplitz identity route. -/
instance (s : Hyperlocal.OffSeed Xi) : XiKappaAt0Nonzero s :=
  ⟨xi_kappaAt0_ne0_from_anchorSeam (s := s)⟩

end XiPacket
end Targets
end Hyperlocal
