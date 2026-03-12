/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticStripRoot.lean

  Strip root for the true-analytic Rec2 corridor.

  Policy:
  * use a single canonical installed producer for
      `XiRow012UpstreamTrueAnalyticStrip`
  * do NOT keep parallel installed strip-upstream adapters alive here
  * keep the strip Rec2 spine theorem-only and unambiguous for typeclass search
-/

import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalyticFromRec2TrueAnalyticStrip

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromRec2AtOrderTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalyticStrip

set_option autoImplicit false
noncomputable section
