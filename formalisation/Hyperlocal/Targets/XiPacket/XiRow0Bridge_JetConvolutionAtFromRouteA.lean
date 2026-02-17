/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetConvolutionAtFromRouteA.lean

  Purpose:
    Make **Leibniz (binomial)** the *primary* Row--0 semantic gate, and provide
    `JetConvolutionAt` for the canonical ξ-windows as a *derived* interface.

  Status:
    Centralises the one shape-change lemma here.

  NOTE:
    This file depends on `JetConvolutionAt` (from Cauchy semantics). If that module
    is currently failing due to a build cycle, you must break the cycle first
    (see grep commands below).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

/-- Bridge: order-2 Leibniz jet semantics implies the Cauchy/jet-convolution predicate. -/
axiom jetConvolutionAt_of_jetLeibnizAt
  (s : _root_.Hyperlocal.OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
  _root_.Hyperlocal.Targets.XiPacket.JetLeibnizAt s z w → JetConvolutionAt s z w

theorem xiJetConvolutionAt_w0  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (w0 s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := rho s) (w := w0 s)
    (xiJetLeibnizAt_w0 (s := s))

theorem xiJetConvolutionAt_wc  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wc s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := rho s) (w := wc s)
    (xiJetLeibnizAt_wc (s := s))

theorem xiJetConvolutionAt_wp2 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wp2 s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := rho s) (w := wp2 s)
    (xiJetLeibnizAt_wp2 (s := s))

theorem xiJetConvolutionAt_wp3 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wp3 s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := rho s) (w := wp3 s)
    (xiJetLeibnizAt_wp3 (s := s))

end JetQuotOp
end XiPacket
end Targets
end Hyperlocal
