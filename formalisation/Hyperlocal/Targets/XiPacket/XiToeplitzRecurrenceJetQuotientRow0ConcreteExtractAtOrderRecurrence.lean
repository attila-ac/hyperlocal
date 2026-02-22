/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderRecurrence.lean

  TEMPORARY SHIM (cycle-safe): route the old “Recurrence” endpoints through the
  now-axiom-free Route–B endpoint `...FromRecurrenceB`.

  CHANGE (2026-02-22):
  * Previously this shim routed through `...Gate` and re-exported the gate axiom
    `xiJetQuotRow0AtOrderConvolutionOut_axiom`.
  * Now that `xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB` is axiom-free,
    we route:
      - scalar goals via `scalarGoalsAtOrder_of_extract`,
      - concrete extract directly via the Route–B endpoint,
      - convolution-out via the gate-from-analytic builder (depends only on the
        Route–B endpoint alias and Route–A witness package).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateFromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
Backwards-compatible name (historical): Row0 convolution-out bundle “from Recurrence”.

Implemented via the GateFromAnalytic builder using the Route–B endpoint
`xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB`.
-/
theorem xiJetQuotRow0AtOrderConvolutionOut_axiom_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0AtOrderConvolutionOut m s :=
  xiJetQuotRow0AtOrderConvolutionOut_fromAnalytic (m := m) (s := s)

/--
Scalar goals at order “from Recurrence”.

Derived purely from the Route–B Type witness by scalarization.
-/
noncomputable def xiJetQuotRow0ScalarGoalsAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ScalarGoalsAtOrder m s :=
  scalarGoalsAtOrder_of_extract (m := m) (s := s)
    (xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB (m := m) (s := s))

/--
Concrete extract at order “from Recurrence”.

Now exactly the Route–B endpoint (axiom-free in current branch).
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
