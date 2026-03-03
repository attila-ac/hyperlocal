/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaAt0NonzeroFromScReNonzero.lean

  Theorem-level derivation:

    [XiScReNonzero s]  →  kappaAt0 s ≠ 0  →  [XiKappaAt0Nonzero s].

  This file is intentionally legacy-free.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAt0Nonzero
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceScReNonzero
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- κ≠0 at order 0 from closed form + `[XiScReNonzero s]`. -/
theorem xi_kappaAt0_ne0_of_scReNonzero (s : Hyperlocal.OffSeed Xi) [XiScReNonzero s] :
    kappaAt0 s ≠ 0 := by
  intro hk0
  -- Closed form at m=0: κ = Re (cderivIter 0 Xi (sc s)).
  have hk :
      kappaAt0 s = (((cderivIter (0 : ℕ) Xi) (sc s))).re := by
    simpa [kappaAt0] using (XiLemmaC_kappa_closedFormAt (m := (0 : ℕ)) (s := s))

  have hRe0 : (((cderivIter (0 : ℕ) Xi) (sc s))).re = 0 :=
    hk.symm.trans hk0

  have : (Xi (sc s)).re = 0 := by
    simpa [cderivIter] using hRe0

  exact (xi_sc_re_ne_zero_of_inst (s := s)) this

/-- Install `XiKappaAt0Nonzero` theorem-level from `[XiScReNonzero s]`. -/
instance (s : Hyperlocal.OffSeed Xi) [XiScReNonzero s] : XiKappaAt0Nonzero s :=
  ⟨xi_kappaAt0_ne0_of_scReNonzero (s := s)⟩

end XiPacket
end Targets
end Hyperlocal
