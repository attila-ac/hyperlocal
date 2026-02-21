/-
  Hyperlocal/Transport/OffSeedStripBridge.lean

  Small constructors / helpers to build an `OffSeedStrip` once strip bounds are
  available in an upstream context.
-/

import Hyperlocal.Transport.OffSeedStrip
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/-- Build a strip-refined seed from an `OffSeed` plus explicit strip bounds. -/
noncomputable def mkOffSeedStrip
    {H : ℂ → ℂ} (s : OffSeed H)
    (hRe_pos : 0 < s.ρ.re) (hRe_lt_one : s.ρ.re < 1) :
    OffSeedStrip H :=
  { toOffSeed := s
    hRe_pos := hRe_pos
    hRe_lt_one := hRe_lt_one }

/-- Equality of `mkOffSeedStrip` is determined solely by the underlying `OffSeed`.
    Proof fields are Prop, hence proof-irrelevant. -/
@[simp] lemma mkOffSeedStrip_eq_iff_toOffSeed
    {H : ℂ → ℂ} (s : OffSeed H)
    (hRe_pos : 0 < s.ρ.re) (hRe_lt_one : s.ρ.re < 1)
    (t : OffSeedStrip H) :
    mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one) = t ↔
      t.toOffSeed = s := by
  constructor
  · intro h
    -- `congrArg` gives `s = t.toOffSeed`; we want `t.toOffSeed = s`
    simpa [mkOffSeedStrip] using (congrArg OffSeedStrip.toOffSeed h).symm
  · intro ht
    rcases t with ⟨t0, ht0_pos, ht0_lt⟩
    -- `ht : t0 = s`
    cases ht
    -- now compare two records with same `toOffSeed := s`; proofs are Prop.
    have hp : hRe_pos = ht0_pos := Subsingleton.elim _ _
    have hl : hRe_lt_one = ht0_lt := Subsingleton.elim _ _
    cases hp
    cases hl
    rfl

/-- Optional converter: returns `some` iff the strip inequalities hold (classically decidable). -/
noncomputable def OffSeed.toOffSeedStrip? {H : ℂ → ℂ} (s : OffSeed H) : Option (OffSeedStrip H) :=
  if hpos : 0 < s.ρ.re then
    if hlt : s.ρ.re < 1 then
      some (mkOffSeedStrip (s := s) (hRe_pos := hpos) (hRe_lt_one := hlt))
    else
      none
  else
    none

@[simp] lemma OffSeed.toOffSeedStrip?_some_iff
    {H : ℂ → ℂ} (s : OffSeed H) (t : OffSeedStrip H) :
    s.toOffSeedStrip? = some t ↔
      (0 < s.ρ.re ∧ s.ρ.re < 1 ∧ t.toOffSeed = s) := by
  classical
  by_cases hpos : 0 < s.ρ.re
  · by_cases hlt : s.ρ.re < 1
    · have hsimp : s.toOffSeedStrip? = some t ↔ t.toOffSeed = s := by
        simp [OffSeed.toOffSeedStrip?, hpos, hlt]
      constructor
      · intro h
        exact ⟨hpos, hlt, hsimp.mp h⟩
      · rintro ⟨_, _, ht⟩
        exact hsimp.mpr ht
    · simp [OffSeed.toOffSeedStrip?, hpos, hlt]
  · simp [OffSeed.toOffSeedStrip?, hpos]

end Hyperlocal
