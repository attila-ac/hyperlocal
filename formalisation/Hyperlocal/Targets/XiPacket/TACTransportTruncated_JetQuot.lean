/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuot.lean

  A *cycle-safe* hook layer:

  - defines a single predicate asserting that the truncated Toeplitz transport
    gives the correct length-N derivative jet *in whatever jet/quotient model*
    you will later formalise (e.g. mod w^N).

  - derives `IsJet3At` for the transported length-3 window from that predicate.

  IMPORTANT:
  This file does NOT claim any analytic Taylor theorem. The predicate is the
  only semantic assumption; later you discharge it in the correct quotient setting.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC

/-- Iterated complex derivative operator (same pattern as in `XiWindowJetPivotDefs`). -/
def cderivIter (m : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (deriv^[m] f)

/-- The length-`N` derivative jet vector at `z`: `Γ j = f^(j)(z)` (raw iterated `deriv`). -/
def jetVec (N : ℕ) (f : ℂ → ℂ) (z : ℂ) : Fin N → ℂ :=
  fun j => cderivIter (j : ℕ) f z

/-- The length-3 transported window obtained by applying the finite transport to the jet vector. -/
def jetWindow3 (f : ℂ → ℂ) (z δ : ℂ) : Transport.Window 3 :=
  fun i => transport 3 δ (jetVec 3 f z) i

/-
  === The ONE semantic bridge predicate ===

  Later you should *prove* this in the correct quotient sense (e.g. mod w^N),
  not as an analytic equality in ℂ.

  For now it is a single class so downstream code depends on *one* knob only.
-/
class JetShiftExactEq (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) : Prop where
  shift : ∀ j : Fin N,
    cderivIter (j : ℕ) f (z + δ) = transport N δ (jetVec N f z) j

/--
Main hook lemma (N=3):

Assuming the *single* bridge predicate, the transported window is a genuine
`IsJet3At` jet for `f` at the shifted point `z+δ`.
-/
theorem isJet3At_jetWindow3_of_shift
    (f : ℂ → ℂ) (z δ : ℂ) [JetShiftExactEq 3 f z δ] :
    IsJet3At f (z + δ) (jetWindow3 f z δ) := by
  classical

  -- index 0
  have h0 :
      transport 3 δ (jetVec 3 f z) (0 : Fin 3) = f (z + δ) := by
    -- start from the bridge equation and simplify the LHS
    have h := JetShiftExactEq.shift (N := 3) (f := f) (z := z) (δ := δ) (j := (0 : Fin 3))
    -- h : cderivIter 0 f (z+δ) = transport ...
    -- simplify cderivIter 0
    simpa [cderivIter, jetVec] using h.symm

  -- index 1
  have h1 :
      transport 3 δ (jetVec 3 f z) (1 : Fin 3) = deriv f (z + δ) := by
    have h := JetShiftExactEq.shift (N := 3) (f := f) (z := z) (δ := δ) (j := (1 : Fin 3))
    -- simplify cderivIter 1
    simpa [cderivIter, jetVec] using h.symm

  -- index 2
  have h2 :
      transport 3 δ (jetVec 3 f z) (2 : Fin 3) = deriv (deriv f) (z + δ) := by
    have h := JetShiftExactEq.shift (N := 3) (f := f) (z := z) (δ := δ) (j := (2 : Fin 3))
    -- simplify cderivIter 2
    -- `simp` needs the iterate expansion for 2
    simpa [cderivIter, jetVec, Function.iterate_succ, Function.iterate_zero] using h.symm

  refine ⟨?_, ?_, ?_⟩
  · -- w 0 = f (z+δ)
    simpa [jetWindow3] using h0
  · -- w 1 = deriv f (z+δ)
    simpa [jetWindow3] using h1
  · -- w 2 = deriv (deriv f) (z+δ)
    simpa [jetWindow3] using h2

end TAC

end XiPacket
end Targets
end Hyperlocal
