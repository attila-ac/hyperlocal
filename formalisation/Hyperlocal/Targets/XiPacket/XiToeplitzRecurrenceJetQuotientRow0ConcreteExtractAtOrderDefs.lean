/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs.lean

  Axiom-free definitions for the AtOrder row-0 jet-quotient concrete extraction cliff.

  This file is PURE DEFINITIONS:
  * Type-level witness bundle: `XiJetQuotRow0ConcreteExtractAtOrder`
  * Prop-level bundled output: `XiJetQuotRow0AtOrderOut`
  * Packaging lemma: `xiJetQuotRow0AtOrderOut_of_extract`

  No semantic axioms here.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Type-level concrete extraction bundle (AtOrder): row–0 Toeplitz annihilation for
`w0At/wp2At/wp3At` at derivative order `m`.
-/
structure XiJetQuotRow0ConcreteExtractAtOrder (m : ℕ) (s : OffSeed Xi) : Type where
  hop_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0
  hop_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0
  hop_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

/--
Route–B semantic output (AtOrder) as a Prop bundle.

This is the shape consumed by the frontier projections.
-/
structure XiJetQuotRow0AtOrderOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0
  hwp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0
  hwp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

/--
Prop-level packaged output derived from the Type-level concrete extract.
-/
theorem xiJetQuotRow0AtOrderOut_of_extract
    (m : ℕ) (s : OffSeed Xi) (E : XiJetQuotRow0ConcreteExtractAtOrder m s) :
    XiJetQuotRow0AtOrderOut m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact E.hop_w0At
  · exact E.hop_wp2At
  · exact E.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
