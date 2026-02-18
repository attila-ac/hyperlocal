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

/-- Route–B frontier (AtOrder): Toeplitz row–0 annihilation for `w0At m`. -/
axiom xiJetQuot_row0_w0At (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0

/-- Route–B frontier (AtOrder): Toeplitz row–0 annihilation for `wp2At m`. -/
axiom xiJetQuot_row0_wp2At (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0

/-- Route–B frontier (AtOrder): Toeplitz row–0 annihilation for `wp3At m`. -/
axiom xiJetQuot_row0_wp3At (m : ℕ) (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

end XiPacket
end Targets
end Hyperlocal
