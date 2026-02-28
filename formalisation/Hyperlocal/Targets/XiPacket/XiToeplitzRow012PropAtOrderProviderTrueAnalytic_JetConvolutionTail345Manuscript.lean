/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript.lean

  Tail345 manuscript gate + adapter to the real Tail345 class.

  FIX (2026-02-28):
  Import the Tail345 *interface* (cycle-safe), NOT JetConvolutionDischarge.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Interface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
Manuscript-facing tail payload:

Same 9 equalities, but kept as a separate class so the proof-producing file
can live “below” the discharge surface in the import DAG.
-/
class XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript : Prop where
  tail3_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0
  tail4_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0
  tail5_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0

  tail3_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0
  tail4_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0
  tail5_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0

  tail3_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0
  tail4_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0
  tail5_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0

/--
Adapter: manuscript tail ⇒ real tail gate.
-/
instance (priority := 1000)
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript] :
    XiJetConvolutionTail345AtOrderTrueAnalytic where
  tail3_w0At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail3_w0At
  tail4_w0At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail4_w0At
  tail5_w0At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail5_w0At
  tail3_wp2At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail3_wp2At
  tail4_wp2At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail4_wp2At
  tail5_wp2At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail5_wp2At
  tail3_wp3At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail3_wp3At
  tail4_wp3At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail4_wp3At
  tail5_wp3At := XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail5_wp3At

end XiPacket
end Targets
end Hyperlocal
