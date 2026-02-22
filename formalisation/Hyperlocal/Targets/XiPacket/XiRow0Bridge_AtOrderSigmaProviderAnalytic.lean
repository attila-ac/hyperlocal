/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderAnalytic.lean

  Analytic-only landing pad for the sigma provider instance (FULL R0 Path A).

  2026-02-22 correction:
  `row0Sigma` depends on coordinate 2 (at least), so it is NOT derivable from coords01 alone.
  Instead we use the intended extractor-free bridge:

      Row0 frontier at order  ⇒  sigma goals

  via:
      XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder.lean

  This deletes the three sigma axioms while keeping the DAG clean.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## The three sigma goals

These are exported under stable names.
They are now obtained from the theorem-level provider instance
installed by `...FromRow0FrontierAtOrder`.
-/

theorem sigma_w0At_analytic
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (w0At m s) = 0 := by
  -- Instance is provided by the imported bridge file.
  simpa using (xiAtOrderSigmaOut_provided (m := m) (s := s)).hw0AtSigma

theorem sigma_wp2At_analytic
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (wp2At m s) = 0 := by
  simpa using (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp2AtSigma

theorem sigma_wp3At_analytic
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (wp3At m s) = 0 := by
  simpa using (xiAtOrderSigmaOut_provided (m := m) (s := s)).hwp3AtSigma

/-- Re-exported sigma payload (theorem-level if the imported provider is). -/
theorem xiAtOrderSigmaOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s :=
  xiAtOrderSigmaOut_provided (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
