/-
  Hyperlocal/Targets/XiPacket/XiWindowJetPivotDefs.lean

  Plan C++J (Jet Pivot): define the order-m central jet and the corresponding
  transported prime windows wp2/wp3 built from that jet.

  No semantic proofs here; just defs.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- m-th complex derivative of `f` via iterating `deriv` as an operator. -/
def cderivIter (m : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (deriv^[m] f)

/-- Order-m central jet at the critical-line anchor `sc s`. -/
def xiCentralJetAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 :=
  ![ cderivIter m Xi (sc s)
   , cderivIter (m + 1) Xi (sc s)
   , cderivIter (m + 2) Xi (sc s) ]

/-- Transported order-m jet window. -/
def w0At (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 :=
  (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (xiCentralJetAt m s)

/-- Prime window built from the order-m transported jet. -/
def wpAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) : Transport.Window 3 := fun i =>
  (w0At m s) i
    + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s i))
    + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s i))

def wp2At (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 := wpAt m s 2
def wp3At (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 := wpAt m s 3

end XiPacket
end Targets
end Hyperlocal
