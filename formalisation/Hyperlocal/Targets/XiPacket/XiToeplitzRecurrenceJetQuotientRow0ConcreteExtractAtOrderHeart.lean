/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart.lean

  Heart contract (cycle-safe admitted boundary).

  CHANGE (Row012 discharge plan):
    Strengthen the heart output to carry, in addition to the row0Sigma equalities,
    the two extra linear constraints (Row012ExtraLin) for each AtOrder window.

  This file remains the *single* admitted boundary for the missing analytic content.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Heart output: the scalar Row0 goal plus the two extra linear constraints
needed to upgrade Row0 reverse convolution to the Row012 stencil.

This is the *only* place we strengthen in the Route–B chain.
-/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  -- existing scalar goals (already used by the frontier)
  hw0AtSigma  : row0Sigma s (w0At m s) = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

  -- NEW: extra linear constraints (what Row012 needs beyond row0Sigma)
  hw0AtExtra  : Row012ExtraLin s (w0At m s)
  hwp2AtExtra : Row012ExtraLin s (wp2At m s)
  hwp3AtExtra : Row012ExtraLin s (wp3At m s)

/--
Admitted analytic heart output (current semantic cliff).

Once the true analytic discharge is proven, replace this axiom by a theorem
with no downstream changes.
-/
axiom xiJetQuotRow0AtOrderHeartOut
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderHeartOut m s

end XiPacket
end Targets
end Hyperlocal
