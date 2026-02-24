/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_ConjDerivativePattern.lean

  Analytic content (no axioms):
  If H satisfies RC: conj (H z) = H (conj z),
  then derivatives commute with conj:
    conj (deriv H z) = deriv H (conj z),
  and similarly for cderivIterAt (snapshot-robust iterated derivative recursion).

  NOTE (snapshot reality):
  * `IsROrC.conj` is not available in this Lean~4.23~rc2 snapshot.
  * We therefore take `conj` to mean `((starRingEnd ℂ) : ℂ → ℂ)`.
  * We use `HasDerivAt.conj_conj` from `Mathlib.Analysis.Calculus.Deriv.Star`.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex

/-- Conjugation on `ℂ` in this snapshot. -/
local notation "conj" => ((starRingEnd ℂ) : ℂ → ℂ)

/-- Snapshot-robust iterated complex derivative operator. -/
def cderivIter : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0,     f => f
  | n + 1, f => cderivIter n (fun z => deriv f z)

@[simp] lemma cderivIter_zero (f : ℂ → ℂ) : cderivIter 0 f = f := rfl
@[simp] lemma cderivIter_succ (n : ℕ) (f : ℂ → ℂ) :
    cderivIter (n+1) f = cderivIter n (fun z => deriv f z) := rfl

/-- Convenient point-evaluation notation. -/
abbrev cderivIterAt (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  cderivIter n f z

/--
Key definitional lemma (pointwise form):

`cderivIter (n+1) H z = deriv (cderivIter n H) z`.
-/
lemma cderivIter_succ_apply : ∀ n : ℕ, ∀ (H : ℂ → ℂ) (z : ℂ),
    cderivIter (n+1) H z = deriv (cderivIter n H) z := by
  intro n
  induction n with
  | zero =>
      intro H z
      simp [cderivIter]
  | succ n ih =>
      intro H z
      -- unfold once, then apply IH to the function `fun t => deriv H t`
      -- IMPORTANT: avoid named args here (your snapshot sometimes loses `H`).
      simpa [cderivIter] using (ih (fun t => deriv H t) z)

/--
RC transport through one derivative.

Assumptions:
* `hDiff : Differentiable ℂ H` (holomorphic regime)
* `hRC : ∀ z, conj (H z) = H (conj z)` (reality / conjugation symmetry)

Conclusion:
`conj (deriv H z) = deriv H (conj z)`.
-/
lemma conj_deriv_eq
    {H : ℂ → ℂ}
    (hDiff : Differentiable ℂ H)
    (hRC : ∀ z : ℂ, conj (H z) = H (conj z))
    (z : ℂ) :
    conj (deriv H z) = deriv H (conj z) := by
  -- HasDerivAt for H at z
  have hHz : HasDerivAt H (deriv H z) z :=
    (hDiff.differentiableAt).hasDerivAt

  -- Derivative of (conj ∘ H ∘ conj) at (conj z) is (conj (deriv H z)).
  have hconjconj :
      HasDerivAt (conj ∘ H ∘ conj) (conj (deriv H z)) (conj z) := by
    -- this lemma exists in your snapshot (`Deriv/Star.lean`)
    simpa using (HasDerivAt.conj_conj (𝕜 := ℂ) (hf := hHz))

  -- Identify (conj ∘ H ∘ conj) = H using RC at (conj w)
  have hfun : (conj ∘ H ∘ conj) = H := by
    funext w
    -- RC at (conj w): conj (H (conj w)) = H (conj (conj w)) = H w
    -- simp knows `(conj (conj w)) = w` for `starRingEnd`.
    simpa [Function.comp] using (hRC (conj w))

  -- Rewrite hconjconj as HasDerivAt H ... at conj z
  have hH_at_conjz : HasDerivAt H (conj (deriv H z)) (conj z) := by
    simpa [hfun] using hconjconj

  -- Standard derivative at conj z
  have hH_std : HasDerivAt H (deriv H (conj z)) (conj z) :=
    (hDiff.differentiableAt).hasDerivAt

  -- Uniqueness of derivative at a point
  exact hH_at_conjz.unique hH_std

/--
RC transport through all iterated derivatives (for TAC.cderivIter recursion).

We assume differentiability of every iterate as an explicit bundle,
mirroring your FE file’s “entire/holomorphic regime” pattern.
-/
lemma conj_cderivIterAt_eq
    {H : ℂ → ℂ}
    (hRC : ∀ z : ℂ, conj (H z) = H (conj z))
    (hDiffIter : ∀ n : ℕ, Differentiable ℂ (cderivIter n H)) :
    ∀ n : ℕ, ∀ p : ℂ,
      conj (cderivIterAt n H p) = cderivIterAt n H (conj p)
  | 0, p => by
      simp [cderivIterAt, hRC p]
  | n+1, p => by
      -- Fn := cderivIter n H
      let Fn : ℂ → ℂ := cderivIter n H

      -- RC for Fn from IH (pointwise)
      have hRCn : ∀ z : ℂ, conj (Fn z) = Fn (conj z) := by
        intro z
        simpa [Fn, cderivIterAt] using (conj_cderivIterAt_eq (n := n) (p := z) hRC hDiffIter)

      -- conj commutes with deriv on Fn
      have hder : conj (deriv Fn p) = deriv Fn (conj p) :=
        conj_deriv_eq (H := Fn) (hDiff := by simpa [Fn] using hDiffIter n) hRCn p

      -- Avoid `simp` recursion-depth: rewrite both sides via the succ-apply lemma.
      have hs1 : cderivIterAt (n+1) H p = deriv Fn p := by
        -- cderivIterAt (n+1) H p = cderivIter (n+1) H p
        -- = deriv (cderivIter n H) p = deriv Fn p
        simpa [Fn, cderivIterAt] using (cderivIter_succ_apply (n := n) (H := H) (z := p))

      have hs2 : cderivIterAt (n+1) H (conj p) = deriv Fn (conj p) := by
        simpa [Fn, cderivIterAt] using (cderivIter_succ_apply (n := n) (H := H) (z := conj p))

      -- Finish
      simpa [hs1, hs2] using hder

end TAC
end XiPacket
end Targets
end Hyperlocal
