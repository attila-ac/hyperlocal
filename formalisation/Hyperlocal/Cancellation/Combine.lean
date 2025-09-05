-- formalisation/Hyperlocal/Cancellation/Combine.lean
import Mathlib.Data.Complex.Basic
import Hyperlocal.Cancellation.Solo      -- Jet6, diagScale
import Hyperlocal.Cancellation.Setup     -- A₀, t₀, diag_nonzero_at_rho'
import Hyperlocal.Cancellation.QCC       -- QCCfun, kernel_QCC_trivial_at_rho', QCCfun_zero
import Hyperlocal.Cancellation.TRC       -- TRCfun, kernel_TRC_trivial_at_rho', TRCfun_zero

noncomputable section
namespace Hyperlocal
namespace Cancellation

open Complex

/-- “Kernel sets” at the canonical point (as plain sets). -/
def KerQ : Set Jet6 := {x | QCCfun A₀ t₀ x = 0}
def KerT : Set Jet6 := {x | TRCfun A₀ t₀ x = 0}
def KerQcapT : Set Jet6 := {x | QCCfun A₀ t₀ x = 0 ∧ TRCfun A₀ t₀ x = 0}

@[simp] lemma mem_KerQ (x : Jet6) : x ∈ KerQ ↔ QCCfun A₀ t₀ x = 0 := Iff.rfl
@[simp] lemma mem_KerT (x : Jet6) : x ∈ KerT ↔ TRCfun A₀ t₀ x = 0 := Iff.rfl
@[simp] lemma mem_KerQcapT (x : Jet6) :
  x ∈ KerQcapT ↔ (QCCfun A₀ t₀ x = 0 ∧ TRCfun A₀ t₀ x = 0) := Iff.rfl

/-- Intersection triviality, stated directly: if both constraints hold, then `x = 0`. -/
theorem Q_and_T_only_zero {x : Jet6}
    (hQ : QCCfun A₀ t₀ x = 0) (_hT : TRCfun A₀ t₀ x = 0) : x = 0 :=
  -- We could use either constraint; QCC already forces `x = 0`.
  kernel_QCC_trivial_at_rho' hQ

/-- Symmetric variant (using TRC alone). -/
theorem T_and_Q_only_zero {x : Jet6}
    (hT : TRCfun A₀ t₀ x = 0) (_hQ : QCCfun A₀ t₀ x = 0) : x = 0 :=
  kernel_TRC_trivial_at_rho' hT

/-- Each kernel is exactly `{0}` (as sets). -/
theorem KerQ_eq_singleton : KerQ = ({0} : Set Jet6) := by
  ext x; constructor
  · intro hx
    -- Use the iff directly instead of `simpa` to please the linter.
    have hx' : QCCfun A₀ t₀ x = 0 := (mem_KerQ x).1 hx
    exact kernel_QCC_trivial_at_rho' hx'
  · intro hx
    -- After `x = 0`, `simp` can discharge membership in the kernel.
    subst hx; simp [KerQ]

theorem KerT_eq_singleton : KerT = ({0} : Set Jet6) := by
  ext x; constructor
  · intro hx
    have hx' : TRCfun A₀ t₀ x = 0 := (mem_KerT x).1 hx
    exact kernel_TRC_trivial_at_rho' hx'
  · intro hx
    subst hx; simp [KerT]

/-- And the intersection is `{0}` as well. -/
theorem KerQcapT_eq_singleton : KerQcapT = ({0} : Set Jet6) := by
  ext x; constructor
  · intro hx  -- from membership to equality
    rcases (mem_KerQcapT x).1 hx with ⟨hQ, _hT⟩
    exact kernel_QCC_trivial_at_rho' hQ
  · intro hx
    -- Zero is in both kernels by `[simp]` lemmas already on `QCCfun_zero` / `TRCfun_zero`.
    subst hx; simp [KerQcapT]

-- Tiny smokes

/-- Zero is in the intersection. -/
example : (0 : Jet6) ∈ KerQcapT := by
  -- Avoid `simpa`: `simp` with the set definition is enough.
  simp [KerQcapT]

/-- If both constraints vanish on `x`, then `x` is the zero jet. -/
example {x : Jet6} (h : x ∈ KerQcapT) : x = 0 := by
  have hQ : QCCfun A₀ t₀ x = 0 := (mem_KerQcapT x).1 h |>.1
  exact kernel_QCC_trivial_at_rho' hQ

end Cancellation
end Hyperlocal
