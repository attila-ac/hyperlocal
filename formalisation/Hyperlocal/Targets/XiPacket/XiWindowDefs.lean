/-
  Hyperlocal/Targets/XiPacket/XiWindowDefs.lean

  Definitional ξ-windows (Plan C++):

    w0  : transported central jet at sc = 1/2 + i t
    wc  : cosine-direction window (MUST NOT be definitional 0)
    ws  : sine-direction window   (MUST NOT be definitional 0)
    wp2 : definitional prime window at p=2 via trig-split coefficients
    wp3 : definitional prime window at p=3 via trig-split coefficients

  This file contains NO semantic proofs. It only pins down rigid definitional objects.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiTransportOp
import Hyperlocal.Transport.JetWindow
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Notation: our concrete target Xi. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- OffSeed coordinates. -/
abbrev σ (s : Hyperlocal.OffSeed Xi) : ℝ := s.ρ.re
abbrev t (s : Hyperlocal.OffSeed Xi) : ℝ := s.ρ.im

/-- Critical-line anchor point sc = 1/2 + i t. -/
def sc (s : Hyperlocal.OffSeed Xi) : ℂ :=
  (1 / 2 : ℝ) + (t s : ℂ) * Complex.I

/-- Central ξ-jet window of length 3 at z: [Xi(z), Xi'(z), Xi''(z)]. -/
def xiJet3At (z : ℂ) : Transport.Window 3 :=
  ![ Xi z, deriv Xi z, deriv (deriv Xi) z ]

/-- Central jet at sc. -/
def xiCentralJet (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 :=
  xiJet3At (sc s)

/-- Transported jet at ρ via XiTransportOp (length 3). -/
def xiTransportedJet (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 :=
  (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (xiCentralJet s)

/-
  Window bundle (Plan C++):

  Right now these are deliberately conservative:
    • `w0` is tied to ξ-data + XiTransportOp by definition
    • the remaining four are deterministic defs you can later refine further,
      but MUST remain definitional objects (not ∃-choices).

  Crucial gate:
    wc/ws must NOT be definitional 0, otherwise κ is definitionally 0.
-/

/-- Base window (transported ξ-jet window). -/
def w0  (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 := xiTransportedJet s

/-
  NOTE (Plan C++): `wc/ws` must not be definitional zero.
  If they are, then κ = det[u0,uc,us] is forced to be 0 by definition,
  and Lemma C (the bCoeff cancellation) becomes impossible.

  We keep them definitional and transport-native by transporting two fixed
  basis windows through `XiTransportOp`.
-/

/-- Standard basis window in `Window 3` at coordinate `j`. -/
def basisW3 (j : Fin 3) : Transport.Window 3 :=
  fun i => if i = j then (1 : ℂ) else 0

-- IMPORTANT: these must not be `private`, otherwise downstream simp cannot decide
-- equalities like `(0 : Fin 3) = e2` when reducing `basisW3 e2`.
abbrev e1 : Fin 3 := ⟨1, by decide⟩
abbrev e2 : Fin 3 := ⟨2, by decide⟩


/-- Cosine-direction window (definitional, nonzero). -/
def wc  (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 :=
  (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (basisW3 e1)

/-- Sine-direction window (definitional, nonzero). -/
def ws  (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 :=
  (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (basisW3 e2)

/-- Prime-column window at p=2 (definitional trig-split form). -/
def wp2 (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 := fun i =>
  (w0 s) i
    + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * ((wc s) i))
    + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * ((ws s) i))

/-- Prime-column window at p=3 (definitional trig-split form). -/
def wp3 (s : Hyperlocal.OffSeed Xi) : Transport.Window 3 := fun i =>
  (w0 s) i
    + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * ((wc s) i))
    + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * ((ws s) i))

end XiPacket
end Targets
end Hyperlocal
