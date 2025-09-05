import Mathlib.Data.Complex.Basic
import Hyperlocal.Cancellation.Solo      -- Jet6, diagScale
import Hyperlocal.Cancellation.Setup     -- A₀, t₀, diag_nonzero_at_rho'
import Hyperlocal.Cancellation.QCC       -- QCCfun
import Hyperlocal.Cancellation.TRC       -- TRCfun

noncomputable section
namespace Hyperlocal
namespace Cancellation

open Complex

-- Handy: zero jet written as a function (helps `simp`).
def zeroJet6 : Jet6 := fun _ => (0 : ℂ)

-- If your TRC/QCC return vector literals like ![ ... ],
-- this lemma lets `simp` close goals of the form `![0,...] i = 0`.
@[simp] lemma vecLit6_zero_eval (i : Fin 6) :
  ((![0, 0, 0, 0, 0, 0] : Jet6) i) = 0 := by
  fin_cases i <;> simp

/-- TRC smoke: zero in ⇒ zero out. -/
example : TRCfun A₀ t₀ (0 : Jet6) = 0 := by
  ext i
  -- Unfold TRCfun pointwise. If TRCfun builds with `![ ... ]`, the lemma above finishes it.
  simp [TRCfun]

/-- QCC smoke: zero in ⇒ zero out. -/
example : QCCfun A₀ t₀ (0 : Jet6) = 0 := by
  ext i
  simp [QCCfun]

end Cancellation
end Hyperlocal
