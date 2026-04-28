import Mathlib.SetTheory.ZFC.Basic
set_option linter.style.whitespace false

/-!
# Presentation 1: Kuratowski Ordered Pair
-/

open ZFSet

/- Definition of the Kuratowski Pair: (x, y) := {x, {x, y}} -/
def kuratowski_pair (x y : ZFSet) : ZFSet :=
  pair (pair x x) (pair x y)

-- Notation for convenience
local notation "⟮" x ", " y "⟯" => kuratowski_pair x y

/--
PROBLEM 1:
Show that for any sets x an y, the ordered pair (x, y) is also a set
We prove this by repeadetly using the Axiom of Pairing, constructively
-/
theorem pair_is_set (x y : ZFSet) : ∃ z : ZFSet, z = ⟮x, y⟯ := by
  -- 1. {x} is a set:
  let s1 := pair x x
  -- 2. {x, y} is a set:
  let s2 := pair x y
  -- 3. {{x}, {x, y}} is a set:
  let s3 := pair s1 s2
  -- We provide s3 as the witness for the existence quantifier
  exists s3

/--
PROBLEM 2:
Prove that if (x, y) = (x', y'), then x = x' and y = y'.
The converse also holds.
-/
theorem pair_eq_iff (x y x' y' : ZFSet) :
    ⟮x, y⟯ = ⟮x', y'⟯ ↔ x = x' ∧ y = y' := by
  constructor
  · -- (⇒) Forward direction
    intro h
    dsimp [kuratowski_pair] at h
    by_cases hxy : x = y
    · -- Case 1 : x = y
      rw [hxy] at h
      sorry
    · -- Case 2 : x ≠ y
      sorry
  · -- (⇐) Backward direction
    intro h
    rcases h with ⟨hx, hy⟩
    rw [hx, hy]
