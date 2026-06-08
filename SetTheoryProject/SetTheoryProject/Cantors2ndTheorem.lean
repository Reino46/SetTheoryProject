/-
**Presentation 11.2: Cantor's 2nd Theorem**
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
set_option linter.style.whitespace false
set_option linter.style.emptyLine false

-- *===============================================================================================*
-- *SETUP: Functions, Bijections, Equinumerous Types,*
-- *DominatedBy Types and Schroeder-Bernstein Theorem*

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

-- e) I define `DominatedBy` (α ≤_c β) meaning there is an injective function from α to β
def DominatedBy (α β : Type) : Prop :=
  ∃ f : α → β, Injective f

local notation α " ≤_c " β => DominatedBy α β

-- f) I introduce the `Schroeder-Bernstein Theorem` as an axiom:
axiom schroeder_bernstein {α β : Type} :
  (α ≤_c β) → (β ≤_c α) → (α =_c β)

-- *===============================================================================================*
-- *DEFINITION 2:*
-- *A `binary sequence` is a function f : ℕ → {0, 1} = 2.*
-- *We write `Δ` for the set of all binary functions*
def Δ := ℕ → Bool

-- *===============================================================================================*
-- *PROBLEM 2:*
-- *Suppose that ∀ n ∈ ℕ, α_n is a binary sequence with elements α_n(0), α_n(1), α_n(2), ...*
-- *We create a new binary sequence β, with β(n) = 1 - α_n(n). Show that β ≠ α^n ∀ n.*

-- I represent the family of sequences α_n as a function `α : ℕ → Δ`.
-- The new sequence β is defined by flipping the n-th bit of the n-th sequence.
-- In Lean, since the sequences return `Bool`, I use `!` (logical NOT) instead of `1 - x`.
def β (α : ℕ → Δ) : Δ :=
  fun n => !(α n n)

#check β

theorem cantor_diagonal (α : ℕ → Δ) (n : ℕ) : β α ≠ α n := by
  -- towards contradiction, suppose they are equal
  intro h_eq
  -- Evaluate both functions at point `n`
  have h_eval := congrFun h_eq n
  dsimp [β] at h_eval
  cases h : α n n
  · rw [h] at h_eval
    contradiction
  · rw [h] at h_eval
    contradiction
  -- Or simply `cases h : α n n <;> simp_all`

-- *===============================================================================================*
-- *PROBLEM 3:*
-- *Using the previous Problem, prove that the set of Binary Sequences (Δ) is uncountable.*
-- *Conclude that ℕ ≠_c ℝ and specifically ℕ <_c ℝ*

-- In Lean, saying a set is uncountable (or strictly larger than ℕ) means there
-- is no surjective function from ℕ to the set
theorem Δ_uncountable : ¬ ∃ (f : ℕ → Δ), Surjective f := by
  -- Suppose the opposite, that there ∃ such f
  intro h_exists

  -- Extract the function f with the proof that it is surjective, `hf`
  rcases h_exists with ⟨f, hf⟩

  dsimp [Surjective] at *

  -- I use β as the y from hf
  have h_beta := hf (β f)

  rcases h_beta with ⟨n, hn_eq⟩

  -- I take the proof that the diagonal is different than the n-th sequence
  have h_neq := cantor_diagonal f n

  rw [hn_eq] at h_neq
  contradiction

-- *--------------------------------------------------------*
-- *Towards the Conclusion ℕ ≠_c ℝ and specifically ℕ <_c ℝ*

-- I define `strictly less cardinality` ( <_c )
def StrictlyDominated (α β : Type) : Prop :=
  (α ≤_c β) ∧ ¬(α =_c β)

local infix:50 " <_c " => StrictlyDominated

-- *I import the properties from Problem 1 and other basic properties as Axioms*

-- Axiom 1 (from Problem 1): ℝ is equinumerous to Δ (set of Binary Sequences)
axiom real_eq_delta : ℝ =_c Δ

-- Axiom 2 (basic property): Equinumerosity is transitive
axiom eq_trans {A B C : Type} : (A =_c B) → (B =_c C) → (A =_c C)

-- Axiom 3 (basic property): Equinumerosity implies that
-- there exists (at least) one surjective function
axiom eq_implies_surj {A B : Type} : (A =_c B) → ∃ (f : A → B), Surjective f

-- Axiom 4 (obvious): There exists an injective function from ℕ to ℝ (e.g. f(n) = n)
axiom nat_dominatedBy_real : ℕ ≤_c ℝ

-- *Now I prove ℕ <_c ℝ*
theorem nat_StrictlyDominated_real : ℕ <_c ℝ := by
  dsimp [StrictlyDominated]
  constructor

  · -- I prove that ℕ ≤_c ℝ
    exact nat_dominatedBy_real

  · -- I prove that ¬ (ℕ =_c ℝ) meaning ℕ ≠_c ℝ
    intro h_eq

    -- Transitivity: since ℕ =_c ℝ and ℝ =_c Δ then ℕ =_c Δ
    have h_N_eq_delta : ℕ =_c Δ := eq_trans h_eq real_eq_delta

    -- Since ℕ =_c Δ, ∃ f : ℕ → Δ, f surjective
    have h_surj : ∃ (f : ℕ → Δ), Surjective f :=
      eq_implies_surj h_N_eq_delta

    -- I use the proof (Cantor diagonal) that there does NOT exist such a function
    have h_not_surj : ¬ ∃ (f : ℕ → Δ), Surjective f :=
      Δ_uncountable

    contradiction
