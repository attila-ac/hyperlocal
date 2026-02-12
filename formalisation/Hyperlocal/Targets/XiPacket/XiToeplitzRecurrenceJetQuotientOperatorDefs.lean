/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorDefs.lean

  Jet-quotient recurrence operator (k=1 lane, Window 3) — DEFINITIONS ONLY.

  This file defines the quartet coefficient function `aR` via elementary symmetric
  sums and builds the lower-triangular Toeplitz operator on Window-3.

  NOTE: This file is *independent* of the semantic interface/axiom file.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Transport.TACToeplitz
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped Real
open Hyperlocal.Transport

namespace JetQuotOp

/-- Quartet roots determined by an off-seed `s`. -/
def rho (s : Hyperlocal.OffSeed Xi) : ℂ := s.ρ
def rhoStar (s : Hyperlocal.OffSeed Xi) : ℂ := star (rho s)
def rhoHat (s : Hyperlocal.OffSeed Xi) : ℂ := (1 : ℂ) - rho s
def rhoHatStar (s : Hyperlocal.OffSeed Xi) : ℂ := star (rhoHat s)

private def r1 (s : Hyperlocal.OffSeed Xi) : ℂ := rho s
private def r2 (s : Hyperlocal.OffSeed Xi) : ℂ := rhoStar s
private def r3 (s : Hyperlocal.OffSeed Xi) : ℂ := rhoHat s
private def r4 (s : Hyperlocal.OffSeed Xi) : ℂ := rhoHatStar s

/-- Elementary symmetric sums σ₁..σ₄ of the quartet roots. -/
def σ1 (s : Hyperlocal.OffSeed Xi) : ℂ := r1 s + r2 s + r3 s + r4 s

def σ2 (s : Hyperlocal.OffSeed Xi) : ℂ :=
  r1 s * r2 s + r1 s * r3 s + r1 s * r4 s +
  r2 s * r3 s + r2 s * r4 s + r3 s * r4 s

def σ3 (s : Hyperlocal.OffSeed Xi) : ℂ :=
  r1 s * r2 s * r3 s +
  r1 s * r2 s * r4 s +
  r1 s * r3 s * r4 s +
  r2 s * r3 s * r4 s

def σ4 (s : Hyperlocal.OffSeed Xi) : ℂ :=
  r1 s * r2 s * r3 s * r4 s

/--
Coefficient function `aR s : ℕ → ℂ` for the monic quartic
`R(z) = ∏(z - root) = z^4 - σ1 z^3 + σ2 z^2 - σ3 z + σ4`.
-/
def aR (s : Hyperlocal.OffSeed Xi) : ℕ → ℂ
  | 0 => σ4 s
  | 1 => - σ3 s
  | 2 => σ2 s
  | 3 => - σ1 s
  | 4 => (1 : ℂ)
  | _ => 0

/-- k=1 lane shift: `ã_j := aR_{1+j}` so the diagonal is `aR_1`. -/
def aRk1 (s : Hyperlocal.OffSeed Xi) (j : ℕ) : ℂ :=
  aR s (j + 1)

/-- Window-3 Toeplitz operator induced by `aRk1`. -/
def jetQuotToeplitzOp3 (s : Hyperlocal.OffSeed Xi) : EndW 2 :=
  toeplitzL 2 (aRk1 s)

end JetQuotOp

/-- Public alias (if you want the old name). -/
abbrev jetQuotToeplitzOp3 (s : Hyperlocal.OffSeed Xi) : EndW 2 :=
  JetQuotOp.jetQuotToeplitzOp3 s

end Hyperlocal.Targets.XiPacket
