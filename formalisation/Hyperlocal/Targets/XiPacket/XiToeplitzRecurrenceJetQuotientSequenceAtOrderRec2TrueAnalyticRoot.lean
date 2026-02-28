/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot.lean

  Strict TRUE-ANALYTIC root import for Front R2:

    Tail345 manuscript payload (+ adapter to real Tail345)
      ⇒ JetConvolutionAtRev discharge
      ⇒ Row012ConvolutionAtRev
      ⇒ Row012Upstream installer
      ⇒ Rec2AtOrder true-analytic instance
-/

-- (If Tail345-from-heart+coords still requires sigma at order, import whichever sigma provider you are using
-- in the strict chain. If you still rely on the axiom installer for sigma, keep this import.)
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderAxiom

-- Provide the *manuscript* Tail345 payload and adapt it to the real Tail345 gate.
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345FromHeartAndCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript

-- Tail345 ⇒ JetConvolutionAtRev
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge

-- JetConvolutionAtRev ⇒ Row012ConvolutionAtRev
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution

-- Installer: Row012ConvolutionAtRev ⇒ Row012Upstream
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalytic

-- Finally: Row012Upstream ⇒ Rec2 interface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
