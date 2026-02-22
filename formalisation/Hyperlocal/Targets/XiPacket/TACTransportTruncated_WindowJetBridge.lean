/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_WindowJetBridge.lean

  Cycle-safe bridge: rewrite the concrete ξ window `w0At` into the finite
  transport stencil `TAC.transportLower`.

  DESIGN:
  * no Row0 semantics / extractor imports
  * only uses the existing window defs and the compat lemma
  * makes *no* analytic claim; the only future semantic knob is isolated
    as a class that you will later discharge in the correct quotient model.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuot
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_XiTransportCompat
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

@[simp] theorem w0At_def (m : ℕ) (s : OffSeed Xi) :
    w0At m s = (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (xiCentralJetAt m s) := by
  rfl

theorem w0At_eq_transportLower (m : ℕ) (s : OffSeed Xi) :
    w0At m s
      =
    (fun i => transportLower 3 ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)
              (xiCentralJetAt m s) i) := by
  classical
  simp [w0At_def, XiTransportOp₂_eq_transportLower]

def w0At_TAC (m : ℕ) (s : OffSeed Xi) : Transport.Window 3 :=
  fun i => transportLower 3 ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)
            (xiCentralJetAt m s) i

@[simp] theorem w0At_eq_w0At_TAC (m : ℕ) (s : OffSeed Xi) :
    w0At m s = w0At_TAC m s := by
  classical
  simpa [w0At_TAC] using (w0At_eq_transportLower (m := m) (s := s))

/--
`JetShiftExactLowerEq m s` is the single semantic assumption that the
transport-lower stencil applied to the central jet equals the *true*
3-jet at the shifted point, in whatever jet/quotient sense you later choose.
-/
class JetShiftExactLowerEq (m : ℕ) (s : OffSeed Xi) : Prop where
  shift0 :
    Xi (sc s + ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))
      = w0At_TAC m s 0
  shift1 :
    deriv Xi (sc s + ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))
      = w0At_TAC m s 1
  shift2 :
    deriv (deriv Xi) (sc s + ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))
      = w0At_TAC m s 2

theorem isJet3At_w0At_of_shiftLower
    (m : ℕ) (s : OffSeed Xi) [JetShiftExactLowerEq m s] :
    IsJet3At Xi (sc s + ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) (w0At m s) := by
  classical
  have hw : w0At m s = w0At_TAC m s := w0At_eq_w0At_TAC (m := m) (s := s)
  refine (hw ▸ ?_)
  refine ⟨?_, ?_, ?_⟩
  · -- need: w0At_TAC m s 0 = Xi(...)
    simpa [w0At_TAC] using (JetShiftExactLowerEq.shift0 (m := m) (s := s)).symm
  · -- need: w0At_TAC m s 1 = deriv Xi (...)
    simpa [w0At_TAC] using (JetShiftExactLowerEq.shift1 (m := m) (s := s)).symm
  · -- need: w0At_TAC m s 2 = deriv (deriv Xi) (...)
    simpa [w0At_TAC] using (JetShiftExactLowerEq.shift2 (m := m) (s := s)).symm

end TAC

end XiPacket
end Targets
end Hyperlocal
