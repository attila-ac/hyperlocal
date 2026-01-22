/-
  Hyperlocal/Transport/ToeplitzOperator.lean

  “Toeplitz operator action” layer, Lean-light:
  operators are plain endomorphisms of Window (n+1).

  No BigOperators / LinearAlgebra imports.
-/

import Hyperlocal.Transport.ToeplitzInterface
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

/-- Endomorphisms of the window space. -/
abbrev EndW (n : ℕ) : Type := Window (n + 1) → Window (n + 1)

namespace EndW

/-- Identity. -/
def id {n : ℕ} : EndW n := fun x => x

/-- Composition (explicit name; avoid field notation headaches). -/
def comp {n : ℕ} (f g : EndW n) : EndW n := fun x => f (g x)

theorem ext {n : ℕ} {f g : EndW n} (h : ∀ x, f x = g x) : f = g := by
  funext x; exact h x

/-- Pointwise zero operator. -/
instance {n : ℕ} : Zero (EndW n) := ⟨fun _ => 0⟩

/-- Pointwise addition. -/
instance {n : ℕ} : Add (EndW n) := ⟨fun f g => fun x => f x + g x⟩

/-- Pointwise scalar multiplication. -/
instance {n : ℕ} : SMul ℂ (EndW n) := ⟨fun a f => fun x => a • f x⟩

@[simp] lemma zero_apply {n : ℕ} (x : Window (n+1)) : (0 : EndW n) x = 0 := rfl
@[simp] lemma add_apply {n : ℕ} (f g : EndW n) (x : Window (n+1)) :
    (f + g) x = f x + g x := rfl
@[simp] lemma smul_apply {n : ℕ} (a : ℂ) (f : EndW n) (x : Window (n+1)) :
    (a • f) x = a • f x := rfl
@[simp] lemma comp_apply {n : ℕ} (f g : EndW n) (x : Window (n+1)) :
    comp f g x = f (g x) := rfl

end EndW

/-- Right shift as an endomorphism. -/
def shiftR_E (n : ℕ) : EndW n := fun x => shiftR x

/-- Left shift as an endomorphism. -/
def shiftL_E (n : ℕ) : EndW n := fun x => shiftL x

/-- Parity as an endomorphism. -/
def parity_E (n : ℕ) : EndW n := fun x => parity x

/-- Parity conjugation: `P ∘ f ∘ P`. (Make `n` explicit to avoid metavariables.) -/
def conjParity (n : ℕ) (f : EndW n) : EndW n :=
  fun x => parity (f (parity x))

/-- Conjugation distributes over addition. -/
lemma conjParity_add (n : ℕ) (f g : EndW n) :
    conjParity n (f + g) = conjParity n f + conjParity n g := by
  funext x i
  -- everything is pointwise in `i : Fin (n+1)`
  simp [conjParity, parity, Pi.add_apply]

/-- Conjugation distributes over scalar multiplication. -/
lemma conjParity_smul (n : ℕ) (a : ℂ) (f : EndW n) :
    conjParity n (a • f) = a • conjParity n f := by
  funext x i
  simp [conjParity, parity, Pi.smul_apply]


/-- Conjugation distributes over composition. -/
lemma conjParity_comp (n : ℕ) (f g : EndW n) :
    conjParity n (EndW.comp f g) = EndW.comp (conjParity n f) (conjParity n g) := by
  funext x
  simp [conjParity, EndW.comp, parity_parity]

/-- Conjugation fixes `id`. -/
lemma conjParity_id (n : ℕ) :
    conjParity n (EndW.id) = (EndW.id : EndW n) := by
  funext x
  simp [conjParity, EndW.id, parity_parity]

/-- Key “equivariance/parity” lemma in operator form: `P ∘ shiftR = shiftL ∘ P`. -/
theorem parity_comp_shiftR_eq_shiftL_comp_parity (n : ℕ) :
    (fun x : Window (n+1) => parity (shiftR x))
      = (fun x : Window (n+1) => shiftL (parity x)) := by
  funext x
  simpa using (parity_shiftR_eq_shiftL_parity (n := n) x)

/-- Conjugating shiftR by parity gives shiftL (by definition of shiftL). -/
lemma conjParity_shiftR (n : ℕ) :
    conjParity n (shiftR_E n) = shiftL_E n := by
  funext x
  -- shiftL is defined as parity (shiftR (parity x))
  simp [conjParity, shiftR_E, shiftL_E, shiftL]

/-- Conjugating shiftL by parity gives shiftR. -/
lemma conjParity_shiftL (n : ℕ) :
    conjParity n (shiftL_E n) = shiftR_E n := by
  funext x
  -- expand shiftL := parity (shiftR (parity ·)) and cancel parity∘parity
  simp [conjParity, shiftR_E, shiftL_E, shiftL, parity_parity]

/--
Toeplitz/shift-generated operators: generated from {0, id, shiftR, shiftL}
under +, scalar multiplication, and composition.
-/
inductive ToeplitzGen (n : ℕ) : EndW n → Prop
| zero : ToeplitzGen n 0
| id   : ToeplitzGen n (EndW.id)
| shiftR : ToeplitzGen n (shiftR_E n)
| shiftL : ToeplitzGen n (shiftL_E n)
| add  {f g} : ToeplitzGen n f → ToeplitzGen n g → ToeplitzGen n (f + g)
| smul {a : ℂ} {f} : ToeplitzGen n f → ToeplitzGen n (a • f)
| comp {f g} : ToeplitzGen n f → ToeplitzGen n g → ToeplitzGen n (EndW.comp f g)

namespace ToeplitzGen

/-- Parity conjugation preserves Toeplitz-generated operators. -/
theorem conjParity_closed {n : ℕ} {f : EndW n} (hf : ToeplitzGen n f) :
    ToeplitzGen n (conjParity n f) := by
  induction hf with
  | zero =>
      simpa [conjParity] using (ToeplitzGen.zero (n := n))
  | id =>
      -- rewrite by conjParity_id
      simpa [conjParity_id (n := n)] using (ToeplitzGen.id (n := n))
  | shiftR =>
      simpa [conjParity_shiftR (n := n)] using (ToeplitzGen.shiftL (n := n))
  | shiftL =>
      simpa [conjParity_shiftL (n := n)] using (ToeplitzGen.shiftR (n := n))
  | add hf hg ihf ihg =>
      -- only 4 binders here: hf hg ihf ihg (NO extra names)
      simpa [conjParity_add (n := n)] using ToeplitzGen.add (n := n) ihf ihg
  | smul hf ih =>
      -- constructor has only {a} {f} + hf
      -- `a` is implicit; keep it implicit and just use simp lemma
      -- Lean will infer `a` from the goal.
      simpa [conjParity_smul (n := n)] using ToeplitzGen.smul (n := n) (f := _) ih
  | comp hf hg ihf ihg =>
      simpa [conjParity_comp (n := n)] using ToeplitzGen.comp (n := n) ihf ihg

end ToeplitzGen

end Transport
end Hyperlocal
