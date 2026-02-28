/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticAdapterFromProvider.lean

  Task-A wiring point:
  Downstream files historically imported this module to obtain an instance of
  `[XiJetQuotRec2AtOrderTrueAnalytic]`.

  The instance is now provided in the dedicated landing pad:
    `XiToeplitzRecurrenceJetQuotientRec2AtOrderTrueAnalytic.lean`.

  This file remains as a stable import path, but contains no additional logic.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRec2AtOrderTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- Intentionally empty: importing the landing pad installs the instance.

end XiPacket
end Targets
end Hyperlocal
