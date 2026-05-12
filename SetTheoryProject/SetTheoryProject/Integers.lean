/-
# Presentation 6: Integers
-/

import Mathlib.Tactic
set_option linter.style.whitespace false
set_option linter.style.emptyLine false

-- *==========================================================================*
-- *DEFINITION 1: Let x, y ε ℕ × ℕ. We define x ~ y if x.1 + y.2 = y.1 + x.2*
def intRel (x y : Nat × Nat) : Prop :=
  x.1 + y.2 = y.1 + x.2

-- *==========================================================================*
-- *PROBLEM 1: Show that `intRel` is an equivalence relation*
-- I use the `Equivalence` typeclass.
theorem intRel_equiv : Equivalence intRel := by
  -- I need 3 properties: reflexivity, symmetry, transitivity
  -- with `Constructor` I break into the main goal into 3 sub-goals
  constructor

  · -- 1. Reflexivity: ∀ x, x ~ x
    intro x
    -- unfold intRel
    rfl
    -- use dsimp [intRel] to see full equation

  · -- 2. Symmetry: ∀ x y, x ~ y → y ~ x
    intro x y h
    dsimp [intRel] at *
    omega

  · -- 3. Transititity ∀ x y z, x ~ y → y ~ z → x ~ z
    intro x y z hxy hyz
    dsimp [intRel] at *
    -- Since we are working with natural numbers and linear equations,
    -- the `omega` tactic can automatically solve this arithmetic system
    -- without manual algebraic manipulation.
    omega

-- *===========================================================================*
-- I use the `Setoid` typeclass which groups
-- the type, the relation, and the equivalence proof together.
-- I define a `Setoid` instance for `ℕ × ℕ` using our relation.
instance intSetoid : Setoid (ℕ × ℕ) where
  r := intRel
  iseqv := intRel_equiv

-- *===========================================================================*
-- *DEFINTION 2 (PART A): The quotient set ℤ = (ℕ × ℕ) / ~*
-- `Integer` instead of Lean's built in `Int`
def Integer : Type := Quotient intSetoid

-- A helper function to easily create an `Integer` from a pair of natural numbers.
-- This corresponds to writing the equivalence class [(n, m)].
-- The `Quotient.mk` (make) function requires a Setoid instance, which it finds automatically
-- because I declared `intSetoid` as an `instance` above.
def Integer.mk (m n : ℕ) : Integer :=
  ⟦(n, m)⟧

-- *===========================================================================*
-- *DEFINITION 2 (PART B): Addition of Integers*

-- 1. I define addition on pairs of natural numbers
def addPair (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1 + b.1, a.2 + b.2)

-- 2. I prove that the operation is well-defined (respects the equivalence relation)
theorem addPair_resp (a₁ a₂ : ℕ × ℕ) (ha : intRel a₁ a₂)
    (b₁ b₂ : ℕ × ℕ) (hb : intRel b₁ b₂) :
    intRel (addPair a₁ b₁) (addPair a₂ b₂) := by
  dsimp [addPair, intRel] at *
  omega

-- 3. Ι lift the operation to the quotient type:
def Integer.add (x y : Integer) : Integer :=
  Quotient.map₂ addPair addPair_resp x y
-- Since integers are equivalence classes, we cannot directly access their representative pairs.
-- `Quotient.map₂` safely applies the operation at the quotient level by requiring the proof
-- (`addPair_resp`) that the addition is well-defined and independent of the chosen representatives.

-- 4. I register the `Add` typeclass instance to enable the standard `+` notation:
instance : Add Integer where
  add := Integer.add

-- *=========================================================================*
-- *DEFINITION 2 (PART C): Multiplication of Integers*

-- 1. Define multiplication on pairs of natural numbers.
def mulPair (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)

-- 2. I prove that the operation respects the equivalence relation (Well-definedness).
theorem mulPair_resp (a₁ a₂ : ℕ × ℕ) (ha : intRel a₁ a₂)
    (b₁ b₂ : ℕ × ℕ) (hb : intRel b₁ b₂) :
    intRel (mulPair a₁ b₁) (mulPair a₂ b₂) := by
  -- Step 1: Unfold definitions
  dsimp [mulPair, intRel] at *
  -- Step 2: This proof is non-linear (involves multiplying variables from hypotheses),
  -- so tactics like `omega` cannot solve it directly.
  -- I transition from Nat to Int to enable subtraction and cleaner algebra
  -- `zify` transforms Nat equalities into Int equalities:
  zify at *
  -- Step 3: I rearrange the hypotheses to represent (n1 - m1) = (n2 - m2):
  have h1 : (a₁.1 : ℤ) - a₁.2 = (a₂.1 : ℤ) - a₂.2 := by linarith
  have h2 : (b₁.1 : ℤ) - b₁.2 = (b₂.1 : ℤ) - b₂.2 := by linarith
  -- Step 4: Prove the goal (it basically is h1 * h2)
  nlinarith

-- 3. I lift the multiplication from pairs to the Integer quotient.
-- Just like addition, I use `Quotient.map₂`.
def Integer.mul (x y : Integer) : Integer :=
  Quotient.map₂ mulPair mulPair_resp x y

-- 4. I register the `Mul` typeclass instance to enable the standard `*` notation.
instance : Mul Integer where
  mul := Integer.mul

-- *==========================================================================*
-- *PROBLEM 2: Prove the following properties:*

-- *1. Associativity of Addition*
theorem Integer.add_assoc (x y z : Integer) : (x + y) + z = x + (y + z) :=
  -- since x, y, z are quotient elements, I use `QuotientInductionOn₃`
  -- to access their representative pairs a, b, c : ℕ × ℕ
  Quotient.inductionOn₃ x y z fun a b c => by
  -- To prove two equivalence classes are equal, `Quotient.sound` reduces
  -- the goal to showing that their inner representatives satisfy `intRel`.
  apply Quotient.sound
  dsimp [addPair]
  change intRel _ _
  dsimp [intRel]
  omega

-- *2. Associativity of Multiplication*
theorem Integer.mul_assoc (x y z : Integer) : (x * y) * z = x * (y * z) :=
  Quotient.inductionOn₃ x y z fun a b c => by
  apply Quotient.sound
  dsimp [mulPair]
  change intRel _ _
  dsimp [intRel]
  -- The goal is now a large non-linear polynomial identity over ℕ.
  -- The `ring` tactic automatically expands and verifies equivalence.
  ring

-- *3. Commutativity of Addition*
theorem Integer.add_comm (x y : Integer) : x + y = y + x :=
  Quotient.inductionOn₂ x y fun a b => by
  apply Quotient.sound
  dsimp [addPair]
  change intRel _ _
  dsimp [intRel]
  omega

-- *4. Commutativity of Multiplication*
theorem Integer.mul_comm (x y : Integer) : x * y = y * x :=
  Quotient.inductionOn₂ x y fun a b => by
  apply Quotient.sound
  dsimp [mulPair]
  change intRel _ _
  dsimp [intRel]
  ring

-- *=======================================================================*
-- *PROBLEM 3: Prove the following properties:*

-- *1. ∃ x ∈ ℤ, ∀ y ∈ ℤ : x + y = y (We write 0 for the element from (1))*

-- I define zero constructively using the simplest representative (0,0)
def Integer.zero : Integer := ⟦(0,0)⟧

-- I register the `Zero` typeclass to enable the standard `0` notation
instance : Zero Integer where
  zero := Integer.zero

-- I prove that 0 + y = y
theorem Integer.zero_add (y : Integer) : 0 + y = y :=
  Quotient.inductionOn y fun b => by
  apply Quotient.sound
  dsimp [addPair]
  change intRel _ _
  dsimp [intRel]
  omega

-- *2. ∃ x ∈ ℤ, ∀ y ∈ ℤ : x * y = y (We write 1 for the element from (2))*

def Integer.one : Integer := ⟦(1,0)⟧

instance : One Integer where
  one := Integer.one

theorem Integer.one_mul (y : Integer) : 1 * y = y :=
  Quotient.inductionOn y fun b => by
  apply Quotient.sound
  dsimp [mulPair]
  change intRel _ _
  dsimp [intRel]
  omega

-- *3. ∃ x ∈ ℤ, ∀ y ∈ ℤ : x + y = 0*

-- Step 1: I define negation in pairs of Natural Numbers
-- meaning: -(n - m) = m - n so that (n, m) → (m, n)
def negPair (a : ℕ × ℕ) : ℕ × ℕ :=
  (a.2, a.1)

-- Step 2: I prove that negation respect the equivalence relation
-- If a₁ ∼ a₂ then negPair(a₁) ∼ negPair(a₂)
theorem negPair_resp (a₁ a₂ : ℕ × ℕ) (h: intRel a₁ a₂) :
    intRel (negPair a₁) (negPair a₂) := by
  dsimp [negPair, intRel] at *
  omega

-- Step 3: I lift the operation to the quotient type:
def Integer.neg (x : Integer) : Integer :=
  Quotient.map negPair negPair_resp x

-- Step 4: I register the `Neg` typeclass instance to enable the standard `-` notation
instance : Neg Integer where
  neg := Integer.neg

-- Step 5: I prove the fundamental cancellation property: x + (-x) = 0
theorem Integer.add_neg_cancel (x : Integer) : x + (-x) = 0 :=
  Quotient.inductionOn x fun a => by
    apply Quotient.sound
    dsimp [negPair, addPair]
    change intRel _ _
    dsimp [intRel]
    omega

-- Step 6: Finally, I prove (3) : ∃ x ∈ ℤ, ∀ y ∈ ℤ : x + y = 0
theorem Integer.exists_neg (x : Integer) : ∃ (y : Integer), x + y = 0 :=
  -- I use the anonymous constructor ⟨witness, proof⟩ (=Exists.intro)
  ⟨-x, Integer.add_neg_cancel x⟩

-- *4. ∀ x, y, z ∈ ℤ : x * (y + z) = x * y + x * z*
theorem Integer.mul_add (x y z : Integer) : x * (y + z) = x * y + x * z :=
  Quotient.inductionOn₃ x y z fun a b c => by
  apply Quotient.sound
  dsimp [addPair, mulPair]
  change intRel _ _
  dsimp [intRel]
  ring

-- *==============================================================================*
-- *CONCLUSION: (ℤ, +, *) is a Commutative Ring*

instance : CommRing Integer where
  add := (· + ·)
  add_assoc := Integer.add_assoc
  zero := 0
  zero_add := Integer.zero_add
  add_zero := by
    intro x
    rw [Integer.add_comm, Integer.zero_add]
  neg := (- ·)
  neg_add_cancel := by
    intro x
    rw [Integer.add_comm, Integer.add_neg_cancel]
  add_comm := Integer.add_comm
  mul := (· * ·)
  mul_assoc := Integer.mul_assoc
  one := 1
  one_mul := Integer.one_mul
  mul_one := by
    intro x
    rw [Integer.mul_comm, Integer.one_mul]
  left_distrib := Integer.mul_add
  right_distrib := by
    intro x y z
    rw [Integer.mul_comm, Integer.mul_add]
    rw [Integer.mul_comm z x, Integer.mul_comm z y]
  mul_comm := Integer.mul_comm
  zero_mul := by
    intro x
    -- `refine` tells Lean: "I'm using induction on x, here is the function (fun a => ...)"
    refine Quotient.inductionOn x (fun a => ?_)
    apply Quotient.sound
    dsimp [mulPair]
    change intRel _ _
    dsimp [intRel]
    omega
  mul_zero := by
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    apply Quotient.sound
    dsimp [mulPair]
    rfl
  -- Natural Scalar Multiplication:
  nsmul := nsmulRec
  -- Integer Scalar Multiplication:
  zsmul := zsmulRec
  -- In Lean's algebraic hierarchy, a Commutative Ring automatically inherits
  -- scalar multiplication by natural numbers (nsmul: ℕ × R → R) and integers (zsmul: ℤ × R → R).
  -- By assigning `nsmulRec` and `zsmulRec`, we instruct Lean to use its built-in,
  -- default recursive definitions for these operations (e.g., 3 * x = x + x + x).
