/-
# Presentation 11.1: Cantor's First Theorem
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs
set_option linter.style.whitespace false
set_option linter.style.emptyLine false

-- *===============================================================================================*
-- *SETUP: Functions, Bijections and Equinumerous Types*

-- a) A function f : α → β is `Injective` (1-1) if f(x₁) = f(x₂) implies x₁ = x₂.
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x₁ x₂ : α, f x₁ = f x₂ → x₁ = x₂

-- b) A function f : α → β is `Surjective` (onto) if every y : β has a pre-image x : α.
def Surjective {α β : Type} (f : α → β) : Prop :=
  ∀ y : β, ∃ x : α, f x = y

-- c) A function is `Bijective` if it is both Injective and Surjective (1-1 and onto).
def Bijective {α β : Type} (f : α → β) : Prop :=
  Injective f ∧ Surjective f

-- d) Two types α and β are `Equinumerous` (α =_c β)
-- if there exists a bijective function between them
def Equinumerous (α β : Type) : Prop :=
  ∃ f : α → β, Bijective f

-- I use the notation `=_c` for Equinumerosity:
local notation α " =_c " β => Equinumerous α β

-- *===============================================================================================*
-- *PROBLEM 1 & 2:*
-- *Prove that ℕ × ℕ =_c ℕ*

-- Cantor's pairing function maps a pair of natural numbers to a single natural number
def cantorPairing (p : ℕ × ℕ) : ℕ :=
  let (n, m) := p
  (n + m) * (n + m + 1) / 2 + m

-- Some checks:
#check cantorPairing
#eval cantorPairing (0, 0) -- f(0,0) = 0 (1st diagonal)
#eval cantorPairing (1, 0) -- f(1,0) = 1 (2nd diagonal)
#eval cantorPairing (0, 1) -- f(0,1) = 2 (2nd diagonal)
#eval cantorPairing (2, 0) -- f(2,0) = 3 (3rd diagonal)
#eval cantorPairing (0, 2) -- f(0,2) = 5 (3rd diagonal)

-- Helper Lemma 1: The sum (n + m) is uniquely determined by the value of f.
lemma cantor_sum_eq {n₁ m₁ n₂ m₂ : ℕ}
    (h : cantorPairing (n₁, m₁) = cantorPairing (n₂, m₂)) :
    n₁ + m₁ = n₂ + m₂ := by
  sorry

-- Helper Lemma 2: If the sums are equal and the values of f are equal, then m₁ = m₂
lemma cantor_m_eq {n₁ m₁ n₂ m₂ : ℕ}
    (h_f : cantorPairing (n₁, m₁) = cantorPairing (n₂, m₂))
    (h_sum : n₁ + m₁ = n₂ + m₂) :
    m₁ = m₂ := by
  dsimp [cantorPairing] at h_f
  rw [h_sum] at h_f
  omega

-- The proof for Injective (1-1)
lemma cantorPairing_Injective : Injective cantorPairing := by
  dsimp [Injective]
  intro p₁ p₂ h_eq

  -- Break p₁, p₂ into their coordinates
  rcases p₁ with ⟨n₁, m₁⟩
  rcases p₂ with ⟨n₂, m₂⟩

  -- The sums are equal from Lemma 1
  have h_sum : n₁ + m₁ = n₂ + m₂ := cantor_sum_eq h_eq

  -- The m's are equal from Lemma 2
  have h_m : m₁ = m₂ := cantor_m_eq h_eq h_sum

  -- Then the n's are equal
  have h_n : n₁ = n₂ := by omega

  -- Then the pairs are the same
  rw [h_m, h_n]

-- The proof for Surjective (onto)
lemma cantorPairing_Surjective : Surjective cantorPairing := by
  dsimp [Surjective]
  intro z
  sorry

-- Finally, I prove Bijective by combining the 2 lemmas
theorem cantorPairing_bijective : Bijective cantorPairing := by
  dsimp [Bijective]
  constructor
  · exact cantorPairing_Injective
  · exact cantorPairing_Surjective

-- *===============================================================================================*
-- *PROBLEM 3:*
-- *Prove that the countable union of countable cets is countable.*

variable {U : Type} -- an arbitrary universe of elements

-- I represent the elements `a_{ji}` as a function `a j i`
-- The Union `⋃A_j` is the set of all elements produced by the function `a`
def UnionSet (a : ℕ → ℕ → U) : Set U :=
  { x : U | ∃ j i : ℕ, a j i = x }

#check UnionSet
#check Set U

-- I define the function `f : ℕ × ℕ → ⋃A_j` with `f(j,i) = a_{ji}` as in the notes
-- **Note:** Because the union is a `Set U`, the output must be a subtype `↥(UnionSet a)`
-- Therefore, I return a pair ⟨value, proof⟩.
def f_union (a : ℕ → ℕ → U) (p : ℕ × ℕ) : ↥(UnionSet a) :=
  ⟨a p.1 p.2, by
    dsimp [UnionSet]
    use p.1, p.2⟩

#check f_union

-- Helper Lemma 1: f is surjective
lemma f_union_surjective (a : ℕ → ℕ → U) : Surjective (f_union a) := by
  dsimp [Surjective]
  intro y

  -- y is a subtype with the property `∃ j i, a j i = y.val`
  -- I extract the indices `j`, `i` and the proof of the equality `h_eq`
  rcases y.property with ⟨j, i, h_eq⟩

  -- I use the pair (j, i) as the witness for the pre-image
  use (j, i)

  -- I use `Subtype.ext` to prove that two subtypes are equal by showing that their values are equal
  apply Subtype.ext

  exact h_eq

-- *------------------------------------------*
-- *SETUP: Domination and Schroeder-Bernstein*

-- I define `DominatedBy` (α ≤_c β) meaning there is an injective function from α to β
def DominatedBy (α β : Type) : Prop :=
  ∃ f : α → β, Injective f

local notation α " ≤_c " β => DominatedBy α β

-- I introduce the `Schroeder-Bernstein Theorem` as an axiom:
axiom schroeder_bernstein {α β : Type} :
  (α ≤_c β) → (β ≤_c α) → (α =_c β)

-- *-----------------------------------------*

-- Helper Lemma 2: If f : α → β is surjective, then β ≤_c α
-- (I construct an injective g : β → α by picking one pre-image for every y)
lemma surjective_implies_dominatedBy {α β : Type} (f : α → β) (hf : Surjective f) :
    β ≤_c α := by
  -- `hf y` is the proof that ∃ x, f x = y
  -- `Classical.choose` extracts one such `x`
  let g : β → α := fun y => Classical.choose (hf y)
  use g

  dsimp [Injective]
  intro y₁ y₂ hg

  -- `Classical.choose_spec` gives me the property of the chosen x: `f x = y`
  have h1 : f (g y₁) = y₁ := Classical.choose_spec (hf y₁)
  have h2 : f (g y₂) = y₂ := Classical.choose_spec (hf y₂)

  rw [← h1, ← h2]
  rw [hg]

-- Helper Lemma 3: Transitivity of domination (if α ≤_c β and β ≤_c γ, then α ≤_c γ)
lemma dominatedBy_trans {α β γ : Type} (h1 : α ≤_c β) (h2 : β ≤_c γ) : α ≤_c γ := by
  rcases h1 with ⟨f, hf⟩
  rcases h2 with ⟨g, hg⟩

  use g ∘ f

  dsimp [Injective] at *
  intro x₁ x₂ heq
  have h_f_eq : f x₁ = f x₂ := hg (f x₁) (f x₂) heq
  exact hf x₁ x₂ h_f_eq

-- Helper Lemma 4: The union is dominated by ℕ
-- I use the fact that `f_union` is surjective (Lemma 1), `cantorPairing` is injective (Problem 1,2)
-- and the transitivity of the `dominatedBy` relation (Lemma 3)
lemma union_dominatedBy_nat (a : ℕ → ℕ → U) :
    ↥(UnionSet a) ≤_c ℕ := by

  -- Since f_union is surjective, UnionSet ≤_c (ℕ × ℕ)
  have h1 : ↥(UnionSet a) ≤_c ℕ × ℕ :=
    surjective_implies_dominatedBy (f_union a) (f_union_surjective a)

  -- From Problem 1, I have that (ℕ × ℕ) =_c ℕ and therefore also (ℕ × ℕ) ≤_c ℕ
  have h2 : (ℕ × ℕ) ≤_c ℕ := by
    use cantorPairing
    exact cantorPairing_Injective

  -- By transitivity, UnionSet ≤_c ℕ
  exact dominatedBy_trans h1 h2

-- Helper Lemma 5: ℕ is dominated by the union (inverse of Lemma 4)
-- To prove this I need to inject ℕ into the first set A_0
-- I assume `h_inj`: the elements of A_0 are distinct (i.e., A_0 is countably infinite)
lemma nat_dominatedBy_union (a : ℕ → ℕ → U) (h_inj : Injective (a 0)) :
    ℕ ≤_c ↥(UnionSet a) := by

  -- I define a function g(n) = a_{0,n} (mapping each n to the n-th element of A_0)
  let g : ℕ → ↥(UnionSet a) := fun n => ⟨a 0 n, by
    dsimp [UnionSet]
    -- the proof that `a 0 n` is in the union: use indices j=0 and i=n
    use 0, n⟩

  use g

  dsimp [Injective]
  intro n₁ n₂ h_eq

  -- `h_eq` says that the two Subtype packages are equal: g(n₁) = g(n₂)
  -- I use `congrArg Subtype.val` to extract the equality for their values
  -- This transforms h_eq into `a 0 n₁ = a 0 n₂`
  have h_val : a 0 n₁ = a 0 n₂ := congrArg Subtype.val h_eq

  -- Since `a 0` is injective (from the assumption h_inj), I conclude n₁ = n₂
  exact h_inj n₁ n₂ h_val

-- Final Conclusion of Problem 3: The union of countably infite sets is countably infinite
theorem union_equinumerous_nat (a : ℕ → ℕ → U) (h_inj : Injective (a 0)) :
    ↥(UnionSet a) =_c ℕ := by

  -- I have Union ≤_c ℕ (from Lemma 4)
  have h1 : ↥(UnionSet a) ≤_c ℕ := union_dominatedBy_nat a

  -- I have ℕ ≤_c Union (from Lemma 5)
  have h2 : ℕ ≤_c ↥(UnionSet a) := nat_dominatedBy_union a h_inj

  -- By Schroeder-Bernstein, they are equinumerous
  exact schroeder_bernstein h1 h2

-- *===============================================================================================*
-- *PROBLEM 4:*
-- *Prove that ℚ =_c ℕ*

-- *Direction 1: ℕ is dominated by ℚ (ℕ ≤_c ℚ)*
-- I construct the obvious injection g(n) = n
lemma nat_dominatedBy_rat : ℕ ≤_c ℚ := by
  -- I explicitly state the coercion from ℕ to ℚ using `(n : ℚ)`
  let g : ℕ → ℚ := fun n => (n : ℚ)
  use g

  dsimp [Injective]
  intro n₁ n₂ h_eq
  change (↑n₁ : ℚ) = (↑n₂ : ℚ) at h_eq

  -- The `norm_cast` tactic strips the coercions and returns the equality to ℕ
  norm_cast at h_eq

-- *Direction 2: ℚ is dominated by ℕ (ℚ ≤_c ℕ)*
-- I will prove ℚ ≤_c ℤ × ℕ ≤_c ℕ × ℕ ≤_c ℕ

-- Helper Lemma 1: ℤ is dominated by ℕ (ℤ ≤_c ℕ)
-- I map non-negative integers to 2z, and negative integers to -2z-1
lemma int_dominatedBy_nat : ℤ ≤_c ℕ := by
  let f : ℤ → ℕ := fun z =>
    if 0 ≤ z then
      2 * z.natAbs
    else
      2 * z.natAbs - 1

  use f

  dsimp [Injective]
  intro z₁ z₂ h_eq

  change (if 0 ≤ z₁ then 2 * z₁.natAbs else 2 * z₁.natAbs -1) =
         (if 0 ≤ z₂ then 2 * z₂.natAbs else 2 * z₂.natAbs -1) at h_eq

  -- `omega` does not automatically split `if-then-else` expressions.
  -- I manually use `split` to branch into cases (positive/negative).
  -- The `<;>` combinator means "apply the next tactic to ALL generated goals".
  -- I split the first if, then the second if, and finally call omega on all 4 cases
  split at h_eq <;> split at h_eq <;> omega

-- Helper Lemma 2: ℚ is dominated by ℤ × ℕ (ℚ ≤_c ℤ × ℕ)
-- In Lean, a rational number `q` os fundamentally a structure consisting of
-- a numerator `q.num` (integer) and a denominator `q.den` (natural)
lemma rat_dominatedBy_int_cross_nat : ℚ ≤_c (ℤ × ℕ) := by
  -- I map each rational `q` to the pair (numerator, denominator)
  let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  use f

  dsimp [Injective]
  intro q₁ q₂ h_eq

  -- `h_eq` says that the pairs are equal: (q₁.num, q₁.den) = (q₂.num, q₂.den)
  -- I extract the equalities of the first and second coordinates
  have h_num : q₁.num = q₂.num := congrArg Prod.fst h_eq
  have h_den : q₁.den = q₂.den := congrArg Prod.snd h_eq

  -- To prove two rational numbers are equal, I use the `Rat.ext` (extensionality) theorem
  -- It says: "2 rational numbers are equal if their numerators and denominators are equal"
  apply Rat.ext
  · exact h_num
  · exact h_den

-- Helper Lemma 3: ℤ × ℕ is dominated by ℕ × ℕ (ℤ × ℕ ≤_c ℕ × ℕ)
lemma int_cross_nat_dominatedBy_nat_cros_nat : (ℤ × ℕ) ≤_c (ℕ × ℕ) := by
  -- I extract the injetive function from ℤ to ℕ (from Lemma 1)
  rcases int_dominatedBy_nat with ⟨f_int, hf_int⟩

  -- I define a function that applies `f_int` to the first coordinate
  -- and leaves the second unchanged
  let g : ℤ × ℕ → ℕ × ℕ := fun p => (f_int p.1, p.2)
  use g

  dsimp [Injective]
  intro p₁ p₂ h_eq

  -- h_eq is currently `g p₁ = g p₂`. Ι use `change` to reveal g,
  change (f_int p₁.1, p₁.2) = (f_int p₂.1, p₂.2) at h_eq

  -- The `injection` tactic automatically breaks and equality of structures (like pairs)
  -- into seperate equalities for each component
  injection h_eq with h1 h2

  -- Since f_int is injective, h1 implies the original integers are equal
  have h1_inj : p₁.1 = p₂.1 := hf_int p₁.1 p₂.1 h1

  -- I prove the pairs are equal using the `ext` tactic (extensionality)
  ext
  · exact h1_inj
  · exact h2

-- Helper Lemma 4: ℚ is dominated by ℕ (ℚ ≤_c ℕ)
lemma rat_dominatedBy_nat : ℚ ≤_c ℕ := by
  -- 1. ℚ ≤_c ℤ × ℕ (Lemma 2)
  have h1 : ℚ ≤_c ℤ × ℕ := rat_dominatedBy_int_cross_nat

  -- 2. ℤ × ℕ ≤_c ℕ × ℕ (Lemma 3)
  have h2 : (ℤ × ℕ) ≤_c (ℕ × ℕ) := int_cross_nat_dominatedBy_nat_cros_nat

  -- 3. ℕ × ℕ ≤_c ℕ (Problem 1 & 2)
  have h3 : (ℕ × ℕ) ≤_c ℕ := by
    use cantorPairing
    exact cantorPairing_Injective

  -- Transitivity
  have h_step : ℚ ≤_c (ℕ × ℕ) := dominatedBy_trans h1 h2
  exact dominatedBy_trans h_step h3

-- THE FINAL THEOREM: ℚ =_c ℕ
theorem rat_equinumerous_nat : ℚ =_c ℕ := by
  have h_fwd : ℚ ≤_c ℕ := rat_dominatedBy_nat
  have h_bwd : ℕ ≤_c ℚ := nat_dominatedBy_rat

  exact schroeder_bernstein h_fwd h_bwd


#print axioms rat_equinumerous_nat
