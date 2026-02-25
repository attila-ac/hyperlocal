/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution.lean

  Manuscript-facing TRUE-ANALYTIC discharge target for the Row012 reverse-stencil arm.

  We do NOT touch sigma/frontier/extractor.

  We define the genuine analytic burden as:

      [XiJetConvolutionAtRevAtOrderTrueAnalytic]
        ⇒ [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
        ⇒ [XiToeplitzRow012PropAtOrderTrueAnalytic]
        ⇒ [XiJetQuotRec2AtOrderTrueAnalytic]
        ⇒ (frontier-free) sigma via Lean-28 glue, downstream.

  The only nontrivial step here is the projection lemma
  `row012ConvolutionAtRev_of_JetConvolutionAtRev` which already exists.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Manuscript-facing analytic gate:

Provide the *full* Cauchy reverse-convolution tail (all n ≥ 3) + factorisation + jet,
for the three canonical AtOrder windows.

This is the right “real analytic” target: FE/RC/factorisation/Route-A jet package
should discharge these three facts.
-/
class XiJetConvolutionAtRevAtOrderTrueAnalytic : Prop where
  jet_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      JetConvolutionAtRev s s.ρ (w0At m s)
  jet_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  jet_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/--
Projection: full JetConvolutionAtRev ⇒ Row012ConvolutionAtRev (just n=3,4,5),
for the three canonical windows.

This gives the exact class your `XiToeplitzRow012PropAtOrderProviderTrueAnalytic.lean`
expects, sigma-free.
-/
instance (priority := 1000)
    [XiJetConvolutionAtRevAtOrderTrueAnalytic] :
    XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by
  refine ⟨?_, ?_, ?_⟩

  · intro m s
    have H : JetConvolutionAtRev s s.ρ (w0At m s) :=
      XiJetConvolutionAtRevAtOrderTrueAnalytic.jet_w0At (m := m) (s := s)
    exact row012ConvolutionAtRev_of_JetConvolutionAtRev (s := s) (z := s.ρ) (w := w0At m s) H

  · intro m s
    have H : JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
      XiJetConvolutionAtRevAtOrderTrueAnalytic.jet_wp2At (m := m) (s := s)
    exact row012ConvolutionAtRev_of_JetConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H

  · intro m s
    have H : JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
      XiJetConvolutionAtRevAtOrderTrueAnalytic.jet_wp3At (m := m) (s := s)
    exact row012ConvolutionAtRev_of_JetConvolutionAtRev
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) H

end XiPacket
end Targets
end Hyperlocal
