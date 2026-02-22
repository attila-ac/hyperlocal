/-
  Hyperlocal/Targets/XiPacket/XiRow012SigmaExtraLinGoalsAtOrderDefs.lean

  Defs-only Prop bundle:

    (row0Sigma = 0) + (Row012ExtraLin)  at the three AtOrder windows.

  Motivation:
  * `n=3` convCoeff goals are equivalent to `row0Sigma = 0` via
      `row0Sigma_eq_convCoeff_rev`.
  * `n=4,5` convCoeff goals are equivalent to the two `Row012ExtraLin` constraints
    via the closed-form rewrite lemmas.

  This bundle is a more semantic upstream target than raw convCoeff goals.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Semantic goals: (sigma=0) + (extraLin) for each AtOrder window. -/
structure XiRow012SigmaExtraLinGoalsAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  -- w0At
  hw0_sigma : row0Sigma s (w0At m s) = 0
  hw0_ex    : Row012ExtraLin s (w0At m s)

  -- wp2At
  hwp2_sigma : row0Sigma s (wp2At m s) = 0
  hwp2_ex    : Row012ExtraLin s (wp2At m s)

  -- wp3At
  hwp3_sigma : row0Sigma s (wp3At m s) = 0
  hwp3_ex    : Row012ExtraLin s (wp3At m s)

end XiPacket
end Targets
end Hyperlocal
