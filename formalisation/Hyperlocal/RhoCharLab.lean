/-
  RhoCharLab.lean
  Minimal lab to 1) inspect codepoints of "rho" vs "ρ",
  and 2) demonstrate a bullet-safe branching pattern so
  you don't fall into the "Unknown identifier rho/ρ" trap.
-/

import Mathlib.Data.Complex.Basic

noncomputable section
open Complex

namespace RhoCharLab

/-- Return Unicode codepoints of a `String` as a list of `Nat`. -/
def codepoints (s : String) : List Nat :=
  s.data.map (fun c => c.toNat)

/-!
Run these `#eval`s. If your editor injected a *look-alike* character,
you'll see **different** numbers than below.

Expected:
* "rho" → [114, 104, 111]  -- r h o
* "ρ"   → [961]            -- Greek small letter rho (U+03C1)
-/
#eval codepoints "rho"
#eval codepoints "ρ"
#eval codepoints "star ρ"
#eval codepoints "oneMinus ρ"

/-!
`rho` (ASCII) and `ρ` (Greek) are **different identifiers**.
This demo uses both in the same scope so you can confirm they coexist.
-/
theorem demo_scope (rho ρ z : ℂ) :
    z = ρ ∨ z = rho ∨ True := by
  -- Use both so they are definitely in scope:
  have _ := rho + ρ
  exact Or.inr (Or.inr trivial)

/-!
**Bullet-safe branching pattern**

If you put a big term after `exact` and *then* tack on named arguments
on *later lines*, Lean treats those later lines as *outside* the bullet
block → `Unknown identifier rho/ρ`.

To avoid that, wrap the term in a `have := ...; exact this`.
-/
theorem branch_pattern_ok (rho ρ z : ℂ) : True := by
  by_cases hz : z = ρ
  · subst hz
    -- SAFE: put the big application inside a `have`, then `exact` it.
    have t : True := by
      exact True.intro
    exact t
  · have t : True := by
      exact True.intro
    exact t

/-
If you instead write:

  by_cases hz : z = ρ
  · subst hz
    exact True.intro
    -- and THEN add more named arguments on new lines (like `(W := …)`),
    -- those lines are parsed at *top-level*, where `rho`/`ρ` are NOT in scope,
    -- producing: `Unknown identifier rho` / `Unknown identifier ρ`.

That’s the exact failure mode you’re seeing in your big file.
-/

end RhoCharLab
end section
