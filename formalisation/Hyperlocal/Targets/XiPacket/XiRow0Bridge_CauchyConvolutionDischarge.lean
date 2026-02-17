/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischarge.lean

  Discharge instances for Route--C Row--0:
    `JetQuotOp.jetConv_w0/wc/wp2/wp3`.

  This file:
    * adds ONE frontier axiom `jetConvolutionAtRev_of_jetLeibniz`
    * proves namespaced theorems `JetQuotOp.jetConv_*` at the correct quartet centers.

  IMPORTANT:
  We do **NOT** rely on the existing `JetQuotOp.xiJetLeibnizAt_*` theorems,
  because they may be stale in compiled artifacts / shadowed.
  Instead we build the required `JetLeibnizAt` instances directly from the
  Route-A package axiom `JetQuotOp.xiRouteA_jetPkg` and the theorem
  `jetLeibnizAt_from_RouteA`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Single semantic frontier: Leibniz jet payload implies reverse Convolution gate. -/
axiom jetConvolutionAtRev_of_jetLeibniz
  (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
  JetLeibnizAt s z w → JetConvolutionAtRev s z w

namespace JetQuotOp

/-!
  We build the needed `JetLeibnizAt` instances **directly** from the Route-A package axiom,
  at the correct quartet centers, then push them through the single frontier axiom above.
-/

/-- `JetLeibnizAt` for `w0` at `z = s.ρ`. -/
private theorem leibniz_w0 (s : OffSeed Xi) : JetLeibnizAt s (s.ρ) (w0 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := s.ρ) (w := w0 s)
    (_root_.Hyperlocal.Targets.XiPacket.JetQuotOp.xiRouteA_jetPkg
      (s := s) (z := s.ρ) (w := w0 s))

/-- `JetLeibnizAt` for `wc` at `z = 1 - s.ρ`. -/
private theorem leibniz_wc (s : OffSeed Xi) : JetLeibnizAt s (1 - s.ρ) (wc s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (1 - s.ρ)) (w := wc s)
    (_root_.Hyperlocal.Targets.XiPacket.JetQuotOp.xiRouteA_jetPkg
      (s := s) (z := (1 - s.ρ)) (w := wc s))

/-- `JetLeibnizAt` for `wp2` at `z = star(s.ρ)` (as `starRingEnd`). -/
private theorem leibniz_wp2 (s : OffSeed Xi) :
    JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (_root_.Hyperlocal.Targets.XiPacket.JetQuotOp.xiRouteA_jetPkg
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s))

/-- `JetLeibnizAt` for `wp3` at `z = 1 - star(s.ρ)` (as `starRingEnd`). -/
private theorem leibniz_wp3 (s : OffSeed Xi) :
    JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetLeibnizAt_from_RouteA (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s)
    (_root_.Hyperlocal.Targets.XiPacket.JetQuotOp.xiRouteA_jetPkg
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s))

/-- `JetConvolutionAtRev` for the canonical window `w0` at `z = s.ρ`. -/
theorem jetConv_w0 (s : OffSeed Xi) :
    JetConvolutionAtRev s (s.ρ) (w0 s) := by
  exact jetConvolutionAtRev_of_jetLeibniz (s := s) (z := s.ρ) (w := w0 s) (leibniz_w0 s)

/-- `JetConvolutionAtRev` for the canonical window `wc` at `z = 1 - s.ρ`. -/
theorem jetConv_wc (s : OffSeed Xi) :
    JetConvolutionAtRev s (1 - s.ρ) (wc s) := by
  exact jetConvolutionAtRev_of_jetLeibniz (s := s) (z := (1 - s.ρ)) (w := wc s) (leibniz_wc s)

/-- `JetConvolutionAtRev` for the canonical window `wp2` at `z = star(s.ρ)`. -/
theorem jetConv_wp2 (s : OffSeed Xi) :
    JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetConvolutionAtRev_of_jetLeibniz (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (leibniz_wp2 s)

/-- `JetConvolutionAtRev` for the canonical window `wp3` at `z = 1 - star(s.ρ)`. -/
theorem jetConv_wp3 (s : OffSeed Xi) :
    JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetConvolutionAtRev_of_jetLeibniz (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s)
    (leibniz_wp3 s)

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
