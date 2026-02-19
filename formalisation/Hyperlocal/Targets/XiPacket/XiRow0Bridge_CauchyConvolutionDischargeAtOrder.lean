/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischargeAtOrder.lean

  Discharge `Row0ConvolutionAtRev` for AtOrder windows.

  This is the key step that lets Task A replace the AtOrder convolution gate axiom
  by a theorem (still depending on Route–A’s jet package axiom for now).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3PayloadAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation
open Hyperlocal.Transport

/-- Build `Row0ConvolutionAtRev` for `w0At` from Route–A jet package + coeff-3 payload. -/
theorem row0ConvolutionAtRev_w0At (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (s.ρ) (w0At m s) := by
  classical
  rcases JetQuotOp.xiRouteA_jetPkg (s := s) (z := s.ρ) (w := w0At m s) with
    ⟨G, hfac, hjet, _, _, _, _⟩
  refine ⟨G, hfac, hjet, ?_⟩
  simpa using (row0ConvCoeff3_eq_zero_w0At (m := m) (s := s))

/-- Build `Row0ConvolutionAtRev` for `wp2At` from Route–A jet package + coeff-3 payload. -/
theorem row0ConvolutionAtRev_wp2At (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  rcases JetQuotOp.xiRouteA_jetPkg (s := s)
      (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) with
    ⟨G, hfac, hjet, _, _, _, _⟩
  refine ⟨G, hfac, hjet, ?_⟩
  simpa using (row0ConvCoeff3_eq_zero_wp2At (m := m) (s := s))

/-- Build `Row0ConvolutionAtRev` for `wp3At` from Route–A jet package + coeff-3 payload. -/
theorem row0ConvolutionAtRev_wp3At (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  rcases JetQuotOp.xiRouteA_jetPkg (s := s)
      (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) with
    ⟨G, hfac, hjet, _, _, _, _⟩
  refine ⟨G, hfac, hjet, ?_⟩
  simpa using (row0ConvCoeff3_eq_zero_wp3At (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
