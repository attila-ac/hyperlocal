/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetConvolutionAtFromRouteA.lean

  Purpose:
    Make **Leibniz (binomial)** the primary Row--0 semantic gate, and provide
    `JetConvolutionAt` for the canonical ξ-windows as a derived interface.

  Fix:
    Use the correct evaluation point `z` for each canonical window:
      w0  at  ρ
      wc  at  1 - ρ
      wp2 at  conj ρ
      wp3 at  1 - conj ρ
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

open Complex
open Hyperlocal.Transport

/-- Bridge: order-2 Leibniz jet semantics implies the Cauchy/jet-convolution predicate. -/
theorem jetConvolutionAt_of_jetLeibnizAt
  (s : _root_.Hyperlocal.OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
  _root_.Hyperlocal.Targets.XiPacket.JetLeibnizAt s z w → JetConvolutionAt s z w := by
  intro hL
  classical
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  refine ⟨G, hfac, hjet, ?_, ?_, ?_⟩
  ·
    -- unfold `Rfun` in the hypothesis (works under application)
    have h0' := h0
    dsimp [_root_.Hyperlocal.Targets.XiPacket.Rfun] at h0'
    exact h0'
  ·
    -- critical point: force unfolding of `Rfun` under `deriv`
    have h1' := h1
    dsimp [_root_.Hyperlocal.Targets.XiPacket.Rfun] at h1'
    exact h1'
  ·
    have h2' := h2
    dsimp [_root_.Hyperlocal.Targets.XiPacket.Rfun] at h2'
    exact h2'

theorem xiJetConvolutionAt_w0  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (w0 s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := rho s) (w := w0 s)
    (xiJetLeibnizAt_w0 (s := s))

theorem xiJetConvolutionAt_wc  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (1 - s.ρ) (wc s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := 1 - s.ρ) (w := wc s)
    (xiJetLeibnizAt_wc (s := s))

theorem xiJetConvolutionAt_wp2 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s)
    (xiJetLeibnizAt_wp2 (s := s))

theorem xiJetConvolutionAt_wp3 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact jetConvolutionAt_of_jetLeibnizAt (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3 s)
    (xiJetLeibnizAt_wp3 (s := s))

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
