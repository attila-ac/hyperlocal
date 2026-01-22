/-
  Hyperlocal/Cancellation/BridgeToInstability.lean
  (fixed names + correct BridgeDataSeed constructor)
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.QCC
import Hyperlocal.Cancellation.TRC
import Hyperlocal.Cancellation.Setup
import Hyperlocal.Cancellation.Solo
import Hyperlocal.Appendix.InstabilityK1

-- We *do* need the API shim here because we refer to WindowedPivotRecSpec.
import Hyperlocal.Cancellation.Bridge
import Hyperlocal.Cancellation.BridgeAPI

noncomputable section
namespace Hyperlocal
namespace Cancellation

/-! ## 0. Strong/global bridge (renamed to avoid clashes)

If you can prove the global property “every nonzero jet is fine-tuned at (A₀,t₀)”,
you can immediately build the original BridgeData expected by
`no_cancellation_if_unstable`.
-/

/-- Strong bridge (global version): if you can prove that *every* nonzero jet
    is fine-tuned at `(A₀,t₀)`, you get the original `BridgeData`. -/
def BridgeWitnessGlobal
    {k : ℕ}
    (x0 : Jet6) (hx0 : x0 ≠ 0)
    (forces_fine_all : ∀ x : Jet6, x ≠ 0 → FineTuned x) :
    BridgeData k A₀ t₀ :=
{ seed_nontrivial := fun _ => ⟨x0, hx0⟩
, forces_fine     := forces_fine_all }

/-! ## 1. Seed-style bridge

Often you only know how to produce *one* nonzero fine-tuned seed under instability.
That suffices for a contradiction given the Combine lemma.
-/

/-- Seed-style bridge: under `UnstableHom`, produce a *nonzero* jet that is
    fine-tuned at `(A₀,t₀)`. -/
structure BridgeDataSeed (k : ℕ) (A t : ℝ) : Prop where
  seed_fine : UnstableHom k A t → ∃ x : Jet6, x ≠ 0 ∧ FineTuned x

/-- Abstract contradiction (seed form): a single nonzero fine-tuned seed,
    together with the Combine-layer “only zero is fine-tuned”, yields `False`. -/
theorem no_cancellation_if_unstable_seed
    {k : ℕ} {A t : ℝ}
    (bridge : BridgeDataSeed k A t)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0)
    [UnstableHom k A t] :
    False := by
  obtain ⟨x, hx0, hfine⟩ := bridge.seed_fine (inferInstance : UnstableHom k A t)
  have hx : x = 0 := combine_only_zero x hfine
  exact hx0 (by simpa using hx)

/-- Constructor (concrete seed): if you already have a *specific* nonzero jet
    `x0` and the two annihilation facts at `(A₀,t₀)`, you immediately obtain
    a seed-style bridge. -/
def BridgeWitnessSeed_of_seed
    {k : ℕ}
    (x0 : Jet6) (hx0 : x0 ≠ 0)
    (hQCC : QCCfun A₀ t₀ x0 = 0)
    (hTRC : TRCfun A₀ t₀ x0 = 0) :
    BridgeDataSeed k A₀ t₀ :=
{ seed_fine := fun _ => ⟨x0, hx0, And.intro hQCC hTRC⟩ }

/-- Constructor (callbacks from instability): if your nonzero seed depends on
    the `UnstableHom` witness, supply a builder `mkSeed` and proofs that QCC
    and TRC vanish on that seed at `(A₀,t₀)`. -/
def BridgeWitnessSeed_of_callbacks
    {k : ℕ}
    (mkSeed : UnstableHom k A₀ t₀ → Jet6)
    (seed_ne : ∀ hU : UnstableHom k A₀ t₀, mkSeed hU ≠ 0)
    (qcc_of_seed : ∀ hU : UnstableHom k A₀ t₀, QCCfun A₀ t₀ (mkSeed hU) = 0)
    (trc_of_seed : ∀ hU : UnstableHom k A₀ t₀, TRCfun A₀ t₀ (mkSeed hU) = 0) :
    BridgeDataSeed k A₀ t₀ :=
{ seed_fine := fun hU =>
    ⟨ mkSeed hU
    , seed_ne hU
    , And.intro (qcc_of_seed hU) (trc_of_seed hU) ⟩ }

-- === Append / replace in Hyperlocal/Cancellation/BridgeToInstability.lean ===

/-- 6-jet cut-out from a coefficient sequence at base index `n0`. -/
def jetOfSeq (G : ℕ → ℂ) (n0 : ℕ) : Jet6 :=
  fun i => G (n0 + i.1)

/-!  Stencils: the exact vanishing facts we need at (A₀,t₀).
     These are *what* the windowed pivot recurrence must imply;
     we carry them as hypotheses so this file stays admit-free. -/
abbrev QCCStencilAt (G : ℕ → ℂ) (n0 : ℕ) : Prop :=
  QCCfun A₀ t₀ (jetOfSeq G n0) = 0

abbrev TRCStencilAt (G : ℕ → ℂ) (n0 : ℕ) : Prop :=
  TRCfun A₀ t₀ (jetOfSeq G n0) = 0

/-- QCC vanishing from a supplied stencil (later derived from `wrec` + `hw`). -/
lemma qcc_of_window
  {R G H : ℕ → ℂ} {k L n0 : ℕ}
  (wrec : Hyperlocal.Cancellation.BridgeAPI.WindowedPivotRecSpec R G H k L)
  (hw   : Hyperlocal.Cancellation.Bridge.WindowUpTo R L)
  (hQCC : QCCStencilAt G n0) :
  QCCfun A₀ t₀ (jetOfSeq G n0) = 0 :=
hQCC

/-- TRC vanishing from a supplied stencil (later derived from `wrec` + `hw`). -/
lemma trc_of_window
  {R G H : ℕ → ℂ} {k L n0 : ℕ}
  (wrec : Hyperlocal.Cancellation.BridgeAPI.WindowedPivotRecSpec R G H k L)
  (hw   : Hyperlocal.Cancellation.Bridge.WindowUpTo R L)
  (hTRC : TRCStencilAt G n0) :
  TRCfun A₀ t₀ (jetOfSeq G n0) = 0 :=
hTRC

/-- Seed-style constructor from *windowed* pivot recurrence:
    builds `seed_fine` using the canonical seed `jetOfSeq G n0`
    once the two stencils are supplied.  Admit-free. -/
def BridgeWitnessSeedFromWindow
  {R G H : ℕ → ℂ} {k L n0 : ℕ}
  (wrec : Hyperlocal.Cancellation.BridgeAPI.WindowedPivotRecSpec R G H k L)
  (hw   : Hyperlocal.Cancellation.Bridge.WindowUpTo R L)
  (hGnz : G n0 ≠ 0)
  (hQCC : QCCStencilAt G n0)
  (hTRC : TRCStencilAt G n0) :
  BridgeDataSeed k A₀ t₀ :=
{ seed_fine := fun _ =>
    by
      -- Nonzero seed: read off coordinate 0 ⇒ `G n0 ≠ 0`.
      have seed_ne : jetOfSeq G n0 ≠ 0 := by
        intro h
        have := congrArg (fun f => f ⟨0, by decide⟩) h
        dsimp [jetOfSeq] at this
        exact hGnz (by simpa using this)
      exact ⟨ jetOfSeq G n0
            , seed_ne
            , And.intro (qcc_of_window wrec hw hQCC) (trc_of_window wrec hw hTRC) ⟩ }

/-! ## 3. Smoke: seed path closes a contradiction for k = 1 ------------------ -/

example
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0)
    (x0 : Jet6) (hx0 : x0 ≠ 0)
    (hQCC : QCCfun A₀ t₀ x0 = 0)
    (hTRC : TRCfun A₀ t₀ x0 = 0) : False := by
  have bridge : BridgeDataSeed 1 A₀ t₀ :=
    BridgeWitnessSeed_of_seed (k := 1) x0 hx0 hQCC hTRC
  haveI : UnstableHom 1 A₀ t₀ := InstabilityK1.instUnstable_k1 A₀ t₀
  exact no_cancellation_if_unstable_seed (k := 1) (A := A₀) (t := t₀)
          bridge combine_only_zero

end Cancellation
end Hyperlocal
end section
