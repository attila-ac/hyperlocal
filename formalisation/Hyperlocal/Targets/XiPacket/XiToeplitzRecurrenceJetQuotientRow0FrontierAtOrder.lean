import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-!
Route–B frontier (AtOrder): theorem-level projections.

These were previously separate axioms. They are now derived from the single
packaged semantic endpoint `xiJetQuotRow0AtOrderOut_fromConcrete`.
-/

/-- Route–B frontier (AtOrder): Toeplitz row–0 annihilation for `w0At m`. -/
theorem xiJetQuot_row0_w0At (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0AtOrderOut_fromConcrete m s).hw0At

/-- Route–B frontier (AtOrder): Toeplitz row–0 annihilation for `wp2At m`. -/
theorem xiJetQuot_row0_wp2At (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0AtOrderOut_fromConcrete m s).hwp2At

/-- Route–B frontier (AtOrder): Toeplitz row–0 annihilation for `wp3At m`. -/
theorem xiJetQuot_row0_wp3At (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0AtOrderOut_fromConcrete m s).hwp3At

end XiPacket
end Targets
end Hyperlocal
