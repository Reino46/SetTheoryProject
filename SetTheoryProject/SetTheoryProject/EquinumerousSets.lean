/-
# Presentation 9: Equinumerous Sets
-/

import Mathlib.Tactic
set_option linter.style.whitespace false
set_option linter.style.emptyLine false

-- *=============================================================================*
-- *DEFINITIONS 1: Functions, Bijections and Equinumerous Types*

-- a) A function f : α → β is Injective (1-1) if f(x₁) = f(x₂) implies x₁ = x₂.
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x₁ x₂ : α, f x₁ = f x₂ → x₁ = x₂

-- b) A function f : α → β is Surjective (onto) if every y : β has a pre-image x : α.
def Surjective {α β : Type} (f : α → β) : Prop :=
  ∀ y : β, ∃ x : α, f x = y

-- c) A function is Bijective if it is both Injective and Surjective (1-1 and onto).
def Bijective {α β : Type} (f : α → β) : Prop :=
  Injective f ∧ Surjective f

-- d) Two types α and β are Equinumerous (α =_c β)
-- if there exists a bijective function between them
def Equinumerous (α β : Type) : Prop :=
  ∃ f : α → β, Bijective f

-- I introduce the notation `=_c` for Equinumerosity:
local notation α " =_c " β => Equinumerous α β

-- *==============================================================================*
-- *PROBLEM 1: Prove that the relation `=_c` satisfies the properties of an Equivalence*
-- *relation (reflexivity, symmetry, transitivity). Is it an Equivalence relation?*

-- 1. Reflexivity: A =_c A
-- Based on the notes, I define f : A → A with f(x) = x
theorem equinumerous_refl {A : Type} : A =_c A := by
  -- In Lean, the identity function f(x) = x is named `id`.
  -- I provide `id` as the witness for the existential quantifier (∃ f).
  use id

  -- Now I need to prove that `id` is Injective and Surjective.
  -- I use `constructor` to split the goals:
  constructor

  · -- Step 1: Prove Injective
    -- Goal: ∀ x₁ x₂, id x₁ = id x₂ → x₁ = x₂
    intro x₁ x₂ h
    exact h

  · -- Step 2: Prove Surjective
    -- Goal: ∀ y, ∃ x, id x = y
    intro y
    -- for any y, I chose x = y
    use y
    rfl

-- 2. Symmetry: A =_c B → B =_c A
-- If there is a bijection f : A → B then I can construct an inverse bijection g : B → A
theorem equinumerous_symm {A B : Type} (h : A =_c B) : B =_c A := by
  -- Unpack h to extract f and its properties:
  rcases h with ⟨f, h_bij⟩
  rcases h_bij with ⟨h_inj, h_surj⟩

  -- To construct the inverse g, I use the Axiom of Choice:
  -- Since `f` is surjective, for any `y : B`, there exists some `x : A` such that `f x = y`.
  -- `Classical.choose` extracts exactly this `x`.
  let g : B → A := fun y => Classical.choose (h_surj y)

  -- `Classical.choose_spec` provides the proof that our chosen `x` satisfies the equation.
  -- In other words, it proves that f(g(y)) = y.
  have h_fg : ∀ y, f (g y) = y := fun y => Classical.choose_spec (h_surj y)

  -- I provide `g` as the witness for the existential quantifier (∃ g).
  use g

  -- Now I must prove that `g` is Bijective (Inj ∧ Surj)
  constructor

  · -- Step 1: Prove that `g` is Injective
    -- Goal: ∀ y₁ y₂, g y₁ = g y₂ → y₁ = y₂
    intro y₁ y₂ h_g
    -- We can prove this using a calculation block (`calc`), which mimics handwritten math.
    calc
    y₁ = f (g y₁) := (h_fg y₁).symm
    _  = f (g y₂) := by rw [h_g]
    _  = y₂       := (h_fg y₂)

  · -- Step 2 : Prove that `g` is Surjective
    -- Goal: ∀ x : A, ∃ y : B, g y = x
    intro x
    -- The natural choice for `y` is `f x`. I use it:
    use f x
    -- The goal is now: g (f x) = x.
    -- I know that f (g (f x)) = f x (by substituting `y` with `f x` in `h_fg`).
    -- Since `f` is injective, f(a) = f(b) implies a = b. I apply this rule.
    apply h_inj
    -- Now the goal perfectly matches `h_fg`
    exact h_fg (f x)

-- 3. Transitivity: A =_c B → B=_c C → A =_c C
theorem equinumerous_trans {A B C : Type} (h1 : A =_c B) (h2 : B =_c C) : A =_c C := by
  rcases h1 with ⟨f, hf_bij⟩
  rcases h2 with ⟨g, hg_bij⟩
  rcases hf_bij with ⟨hf_inj, hf_surj⟩
  rcases hg_bij with ⟨hg_inj, hg_surj⟩

  -- I use the composition `g ∘ f` as the witness for A =_c C
  use g ∘ f
  constructor

  · -- Step 1: Prove that `g ∘ f` is Injective
    -- Goal: ∀ x₁ x₂, (g ∘ f) x₁ = (g ∘ f) x₂ → x₁ = x₂
    intro x₁ x₂ h_gf
    -- By definition of composition, g(f(x₁)) = g(f(x₂))
    -- Since g is injective f(x₁) = f(x₂)
    have h_f : f x₁ = f x₂ := hg_inj (f x₁) (f x₂) h_gf
    exact hf_inj x₁ x₂ h_f

  · -- Step 2: Prove that `g ∘ f` is Surjective
    -- Goal: ∀ z : C, ∃ x : A, (g ∘ f) x = z
    intro z
    -- Since g is surjective, ∃ y : B such that g(y) = z.
    rcases hg_surj z with ⟨y, hy⟩
    -- Since f is surjective, ∃ x : A such that f(x) = y.
    rcases hf_surj y with ⟨x, hx⟩
    -- I use this x as the witness
    use x
    -- Goal: (g ∘ f) x = z
    -- I substitute y and z using the proofs hx and hy
    calc
      (g ∘ f) x = g (f x) := rfl
      _         = g y := by rw [hx]
      _         = z := by rw [hy]

/-
  *NOTE: The relation `=_c` is NOT an equivalence relation.*
  An equivalence relation must be a subset of a Cartesian product (A × A) of a set A.
  `=_c` is defined on the class of *ALL SETS* !
-/

-- *=====================================================================================*
-- *PROBLEM 2:*
