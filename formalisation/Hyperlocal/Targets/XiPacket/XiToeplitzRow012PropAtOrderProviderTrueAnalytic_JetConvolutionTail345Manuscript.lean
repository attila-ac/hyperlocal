/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript.lean

  Manuscript-facing analytic interface for the ONLY real obligations in the
  JetConvolution tail proof:

    convCoeff (row0CoeffSeqRev s) (winSeqRev (w?At m s)) n = 0
  for n = 3,4,5 and w?At ∈ {w0At, wp2At, wp3At}.

  This file is GREEN:
  - no sigma / no frontier / no extractor
  - no sorry / no axioms

  Usage:
    The manuscript analytics should eventually provide an instance of
      [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript].
    Then the adapter instance below automatically provides
      [XiJetConvolutionTail345AtOrderTrueAnalytic]
    which your JetConvolutionDischarge file consumes.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Cancellation.Recurrence

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
MANUSCRIPT INTERFACE (green):

Provide the 9 vanishing Cauchy coefficients (n = 3,4,5) for the three canonical windows.
This is the exact “real analytic” content to discharge from FE/RC/factorisation/Route–A.
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

/-!
### Nine lemma names (nice API)

These are just projections of the manuscript class fields.
They’re what you’ll actually “fill” later by providing an instance of the class.
-/

theorem tail3_w0At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail3_w0At (m := m) (s := s)

theorem tail4_w0At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail4_w0At (m := m) (s := s)

theorem tail5_w0At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail5_w0At (m := m) (s := s)

theorem tail3_wp2At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail3_wp2At (m := m) (s := s)

theorem tail4_wp2At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail4_wp2At (m := m) (s := s)

theorem tail5_wp2At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail5_wp2At (m := m) (s := s)

theorem tail3_wp3At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail3_wp3At (m := m) (s := s)

theorem tail4_wp3At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail4_wp3At (m := m) (s := s)

theorem tail5_wp3At_trueAnalytic
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript]
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0 :=
  XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript.tail5_wp3At (m := m) (s := s)

/--
Adapter:
  manuscript 9-facts → the gate consumed by your JetConvolutionDischarge file.
-/
instance (priority := 1000)
    [XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript] :
    XiJetConvolutionTail345AtOrderTrueAnalytic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m s; exact tail3_w0At_trueAnalytic (m := m) (s := s)
  · intro m s; exact tail4_w0At_trueAnalytic (m := m) (s := s)
  · intro m s; exact tail5_w0At_trueAnalytic (m := m) (s := s)

  · intro m s; exact tail3_wp2At_trueAnalytic (m := m) (s := s)
  · intro m s; exact tail4_wp2At_trueAnalytic (m := m) (s := s)
  · intro m s; exact tail5_wp2At_trueAnalytic (m := m) (s := s)

  · intro m s; exact tail3_wp3At_trueAnalytic (m := m) (s := s)
  · intro m s; exact tail4_wp3At_trueAnalytic (m := m) (s := s)
  · intro m s; exact tail5_wp3At_trueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
