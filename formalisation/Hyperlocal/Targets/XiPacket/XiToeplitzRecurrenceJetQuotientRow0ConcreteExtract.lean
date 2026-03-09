/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract.lean

  Concrete recurrence-extraction frontier (Route B, jet-quotient).

  This file packages the row-0 concrete Toeplitz annihilation facts coming from
  `XiToeplitzRecurrenceJetQuotientRow0Concrete.lean`.

  IMPORTANT:
  * In the current build-green snapshot, `XiToeplitzRecurrenceJetQuotientRow0Concrete`
    is still the historical ungated producer for `wc`.
  * Therefore this consumer must also remain ungated.
  * Do NOT add `[TAC.XiJetWindowEqAtOrderQuotProvider]` here until the actual
    producer swap in `...Row0Concrete.lean` is committed and all downstream
    consumers are migrated coherently.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Concrete
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
Bundled row-0 concrete extract for the four canonical Route-B windows.
-/
structure XiJetQuotRow0ConcreteExtract (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

/--
The four canonical ξ windows used by the row-0 Route-B concrete extractor.
-/
inductive XiJetQuotCanonicalWindow (s : Hyperlocal.OffSeed Xi) : Window 3 → Prop
  | w0  : XiJetQuotCanonicalWindow s (w0 s)
  | wc  : XiJetQuotCanonicalWindow s (wc s)
  | wp2 : XiJetQuotCanonicalWindow s (wp2 s)
  | wp3 : XiJetQuotCanonicalWindow s (wp3 s)

/--
Case-split wrapper around the four concrete row-0 lemmas.
-/
theorem xiJetQuot_row0_of_canonical
    (s : Hyperlocal.OffSeed Xi) {w : Window 3} :
    XiJetQuotCanonicalWindow s w →
      (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
  intro hw
  cases hw with
  | w0  => simpa using xiJetQuot_row0_w0  (s := s)
  | wc  => simpa using xiJetQuot_row0_wc  (s := s)
  | wp2 => simpa using xiJetQuot_row0_wp2 (s := s)
  | wp3 => simpa using xiJetQuot_row0_wp3 (s := s)

/--
Package the canonical-window row-0 identities into the bundled extract.
-/
def xiJetQuotRow0ConcreteExtract
    (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ConcreteExtract s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.w0  (s := s))
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.wc  (s := s))
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.wp2 (s := s))
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.wp3 (s := s))

/--
Operator-branded row-0 canonical-window fact.
-/
theorem xiJetQuot_op3_fin0_of_canonical
    (s : Hyperlocal.OffSeed Xi) {w : Window 3} :
    XiJetQuotCanonicalWindow s w →
      (JetQuotOp.jetQuotToeplitzOp3 s w) (0 : Fin 3) = 0 := by
  intro hw
  simpa [JetQuotOp.jetQuotToeplitzOp3] using
    (xiJetQuot_row0_of_canonical (s := s) (w := w) hw)

end XiPacket
end Targets
end Hyperlocal
