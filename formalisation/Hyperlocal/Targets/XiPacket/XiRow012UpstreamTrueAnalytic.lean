/-
  Hyperlocal/Targets/XiPacket/XiRow012UpstreamTrueAnalytic.lean

  TRUE-ANALYTIC upstream installer for the Row012 reverse-stencil convolution payload:

    XiRow012UpstreamTrueAnalytic.row012_out :
      ∀ m s, XiRow012ConvolutionAtRevAtOrderOut m s

  DESIGN:
  * Rec2-free
  * Extractor-free
  * Imports only the true-analytic JetConvolution discharge chain and the Row012 output interface.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface

-- This pair is your existing true-analytic pipeline:
--   JetConvolution discharge  ⇒  XiRow012ConvolutionAtRevAtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Upstream rail: package the already sigma-free Row012-at-order convolution facts
as the `XiRow012ConvolutionAtRevAtOrderOut` bundle.

This is the clean extractor-free target: once this instance is available,
everything downstream that expects `[XiRow012UpstreamTrueAnalytic]` can fire
without importing Rec2 or any frontier modules.
-/
instance (priority := 1000)
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic] :
    XiRow012UpstreamTrueAnalytic where
  row012_out := by
    intro m s
    refine ⟨?_, ?_, ?_⟩
    · exact XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At  (m := m) (s := s)
    · exact XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s)
    · exact XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp3At (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
