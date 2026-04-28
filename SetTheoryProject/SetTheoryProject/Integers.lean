/-
# Presentaion 6: Integers
-/

import Mathlib.Tactic
set_option linter.style.whitespace false
set_option linter.style.emptyLine false

-- DEFINITION 1: Let x, y ε ℕ × ℕ. We define x ~ y if x.1 + y.2 = y.1 + x.2
def intRel (x y : Nat × Nat) : Prop :=
  x.1 + y.2 = y.1 + x.2

-- PROBLEM 1: Show that 'intRel' is an equivalnce relation
-- I use the 'Equivalence' typeclass.
theorem intRel_equiv : Equivalence intRel := by
  -- I need 3 properties: relexivity, symmetry, transitivity
  -- with 'Constructor' I break into the main goal into 3 sub-goals
  constructor

  · -- 1. Reflexivity: ∀ x, x ~ x
    intro x
    -- unfold intRel
    rfl
    -- use dsimp [intRel] to see full equation

  · -- 2. Symmetry: ∀ x y, x ~ y → y ~ x
    intro x y h
    dsimp [intRel] at *
    --the symmetry of equality provides the goal directly from h
    exact h.symm

  · -- 3. Transiitity ∀ x y z, x ~ y → y ~ z → x ~ z
    intro x y z hxy hyz
    dsimp [intRel] at *
    -- Since we are working with natural numbers and linear equations,
    -- the `omega` tactic can automatically solve this arithmetic system
    -- without manual algebraic manipulation.
    omega


-- I use the `Setoid` typeclass which groups
-- the type, the relation, and the equivalence proof together.
-- I define a `Setoid` instance for `ℕ × ℕ` using our relation.
instance intSetoid : Setoid (ℕ × ℕ) where
  r := intRel
  iseqv := intRel_equiv


-- DEFINTION 2: The quotient set ℤ = (ℕ × ℕ) / ~
-- `Integer` instead of Lean's built in `Int`
def Integer : Type := Quotient intSetoid

-- A helper function to easily create an `Integer` from a pair of natural numbers.
-- This corresponds to writing the equivalence class [(n, m)].
-- The `Quotient.mk` (make) function requires a Setoid instance, which it finds automatically
-- because I declared `intSetoid` as an `instance` above.
def Integer.mk (m n : ℕ) : Integer :=
  Quotient.mk intSetoid (n , m)

-- We can also define a local notation ⟦x⟧ (typed with \[[ and \]])
-- to represent the equivalence class of x
local notation "⦃" x "⦄" => Quotient.mk intSetoid x
