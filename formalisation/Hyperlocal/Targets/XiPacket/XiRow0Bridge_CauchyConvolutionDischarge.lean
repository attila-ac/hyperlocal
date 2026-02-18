/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischarge.lean

  Temporary discharge instances for Route--C Row--0.

  Frontier is ONE axiom:
    `jetConvolutionAtRev_of_jetLeibniz : JetLeibnizAt -> JetConvolutionAtRev`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace JetQuotOp

/-- Single semantic frontier (temporary): Leibniz payload implies reverse convolution gate. -/
axiom jetConvolutionAtRev_of_jetLeibniz
  (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
  JetLeibnizAt s z w → JetConvolutionAtRev s z w

theorem jetConv_w0 (s : OffSeed Xi) : JetConvolutionAtRev s s.ρ (w0 s) := by
  exact jetConvolutionAtRev_of_jetLeibniz (s := s) (z := s.ρ) (w := w0 s)
    (xiJetLeibnizAt_w0 (s := s))

theorem jetConv_wc (s : OffSeed Xi) : JetConvolutionAtRev s (1 - s.ρ) (wc s) := by
  exact jetConvolutionAtRev_of_jetLeibniz (s := s) (z := (1 - s.ρ)) (w := wc s)
    (xiJetLeibnizAt_wc (s := s))

theorem jetConv_wp2 (s : OffSeed Xi) :
    JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetConvolutionAtRev_of_jetLeibniz
      (s := s) (z := ((starRingEnd ℂ) s.ρ)) (w := wp2 s)
      (xiJetLeibnizAt_wp2 (s := s))

theorem jetConv_wp3 (s : OffSeed Xi) :
    JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetConvolutionAtRev_of_jetLeibniz
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s)
      (xiJetLeibnizAt_wp3 (s := s))

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
