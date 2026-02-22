/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderAnalytic.lean

  Analytic-only landing pad for the sigma provider instance (FULL R0 Path A).

  Goal: replace the remaining sigma axiom instance by a theorem-level instance:
    instance : XiAtOrderSigmaProvider

  DAG contract:
  * Only "true analytic" imports (FE/RC/factorisation/jet identities).
  * MUST NOT import extractor/heart/Route–C landing/discharge modules.

  Today this file contains three local axioms (one per window) to keep the API stable.
  Replace them one-by-one by real analytic theorems, then delete the axioms.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-!
## The three analytic sigma subgoals (true analytic surface)

These are exactly what must be proven theorem-level (no extractor imports):
  row0Sigma s (w0At m s)  = 0
  row0Sigma s (wp2At m s) = 0
  row0Sigma s (wp3At m s) = 0
-/

axiom sigma_w0At_analytic
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (w0At m s) = 0

axiom sigma_wp2At_analytic
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (wp2At m s) = 0

axiom sigma_wp3At_analytic
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (wp3At m s) = 0

/-- Theorem-level sigma bundle (once axioms above are discharged, this is too). -/
theorem xiAtOrderSigmaOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s :=
  ⟨sigma_w0At_analytic (m := m) (s := s),
   sigma_wp2At_analytic (m := m) (s := s),
   sigma_wp3At_analytic (m := m) (s := s)⟩

/-- The theorem-level analytic sigma provider instance (currently staged). -/
instance : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_fromAnalytic

end XiPacket
end Targets
end Hyperlocal
