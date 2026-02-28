/-
  Scratch/PrintWindows.lean

  Usage:
    lake env lean formalisation/Scratch/PrintWindows.lean
  Or open in VSCode.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot

set_option pp.universes true
set_option pp.all true
set_option pp.explicit true
set_option autoImplicit false

namespace Scratch

open Hyperlocal
open Hyperlocal.Transport
open Hyperlocal.Targets
open Hyperlocal.Targets.XiPacket
open Complex

#synth Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic
#synth Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalytic
#synth Hyperlocal.Targets.XiPacket.XiJetConvolutionAtRevAtOrderTrueAnalytic

#check Hyperlocal.Targets.XiPacket.JetQuotOp.xiJetLeibnizAt_wc
#check Hyperlocal.Targets.XiPacket.JetQuotOp.xiRouteA_jetPkg_wc

-- Windows (base)
#check w0
#print w0
#check wc
#print wc
#check wp2
#print wp2
#check wp3
#print wp3

-- Jet pivot windows
#check w0At
#print w0At
#check wpAt
#print wpAt
#check wp2At
#print wp2At
#check wp3At
#print wp3At

-- jet3 (NOTE: lives in XiPacket, not TAC)
#check jet3
#print jet3

-- Route-A quotient
#check routeA_G
#print routeA_G

-- quotient jet predicate(s)
#check IsJet3AtOrderQuot
#print IsJet3AtOrderQuot

end Scratch
