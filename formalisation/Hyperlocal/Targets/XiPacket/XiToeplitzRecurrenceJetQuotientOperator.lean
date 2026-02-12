/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperator.lean

  Jet-quotient recurrence operator (k=1 lane, Window 3) — DEFINITIONS.

  Key point: we use the *centered* quartet polynomial
    R̃(u) := R(ρ + u)
  so that R̃(0)=0 and the k=1 lane starts on the linear coefficient.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.MinimalModel
import Hyperlocal.Transport.TACToeplitz
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

namespace JetQuotOp

/-- Seed root from an off-seed. -/
def rho (s : Hyperlocal.OffSeed Xi) : ℂ := s.ρ

/--
Centered quartet polynomial:
`R̃(u) = quartetPoly(ρ)` evaluated at `u + ρ`, i.e. `R̃(u)=R(ρ+u)`.
-/
def RpolyCentered (s : Hyperlocal.OffSeed Xi) : Polynomial ℂ :=
  (Hyperlocal.MinimalModel.quartetPoly (rho s)).comp (Polynomial.X + Polynomial.C (rho s))

/-- Coefficient function `aR s : ℕ → ℂ` for the centered quartet polynomial. -/
def aR (s : Hyperlocal.OffSeed Xi) (n : ℕ) : ℂ :=
  (RpolyCentered s).coeff n

/-- k=1 lane tail: `ã_j := aR_{j+1}` (diagonal coefficient is `aR 1`). -/
def aRk1 (s : Hyperlocal.OffSeed Xi) (j : ℕ) : ℂ :=
  aR s (j + 1)

/-- Window-3 (n=2) lower Toeplitz operator induced by the k=1 lane coefficients. -/
def jetQuotToeplitzOp3 (s : Hyperlocal.OffSeed Xi) : EndW 2 :=
  toeplitzL 2 (aRk1 s)

end JetQuotOp

-- Public name (keep your downstream naming stable if you want):
abbrev jetQuotToeplitzOp3 (s : Hyperlocal.OffSeed Xi) : EndW 2 :=
  JetQuotOp.jetQuotToeplitzOp3 s

end XiPacket
end Targets
end Hyperlocal
