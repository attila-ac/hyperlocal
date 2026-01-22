/-
  Hyperlocal/Manuscript.lean

  Umbrella import in (rough) manuscript order.
  This file has no code — it just pulls in the whole development
  so `lake build Hyperlocal.Manuscript` acts as a "one-button" build.
-/

import Hyperlocal.Core
import Hyperlocal.MinimalModel

import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Hyperlocal.FactorizationGofSAnalytic
import Hyperlocal.FactorizationGofSEntire

import Hyperlocal.GrowthOrder
import Hyperlocal.Transcendence
import Hyperlocal.FactorizationConsequences

-- Cancellation / Recurrence stack
import Hyperlocal.Cancellation.Solo
import Hyperlocal.Cancellation.Solo12
import Hyperlocal.Cancellation.Setup
import Hyperlocal.Cancellation.QCC
import Hyperlocal.Cancellation.TRC
import Hyperlocal.Cancellation.Combine
import Hyperlocal.Cancellation.Rank
import Hyperlocal.Cancellation.Recurrence
import Hyperlocal.Cancellation.RecurrenceWithFinsetSum
import Hyperlocal.Cancellation.Bridge
import Hyperlocal.Cancellation.BridgeToInstability
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Appendix.InstabilityK1
import Hyperlocal.Appendix.InstabilityK2
import Hyperlocal.Cancellation.WrapUp

-- If you added the Schur–Cohn skeleton under Cancellation, import it here too:
-- import Hyperlocal.Cancellation.SchurCohn
