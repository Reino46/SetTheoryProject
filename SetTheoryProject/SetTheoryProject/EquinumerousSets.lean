/-
# Presentation 9: Equinumerous Sets
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- *=============================================================================*
-- *DEFINITIONS 1: Functions, Bijections and Equinumerous Types*

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

-- I introduce the notation `=_c` for Equinumerosity:
local notation α " =_c " β => Equinumerous α β

-- *======================================================================================================*
-- *PROBLEM 1:*
-- *Prove that the relation =_c satisfies the properties of an Equivalence relation*
-- *(reflexivity, symmetry, transitivity). Is it an Equivalence relation?*

-- 1. Reflexivity: A =_c A
-- Based on the notes, I define f : A → A with f(x) = x
theorem equinumerous_refl {A : Type} : A =_c A := by
  -- In Lean, the identity function f(x) = x is named `id`.
  -- I provide id as the witness for the existential quantifier (∃ f).
  use id

  -- Now I need to prove that id is Injective and Surjective.
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
  -- Since f is surjective, for any y : B, there exists some x : A such that f x = y.
  -- `Classical.choose` extracts exactly this x.
  let g : B → A := fun y => Classical.choose (h_surj y)

  -- `Classical.choose_spec` provides the proof that our chosen x satisfies the equation.
  -- In other words, it proves that f(g(y)) = y.
  have h_fg : ∀ y, f (g y) = y := fun y => Classical.choose_spec (h_surj y)

  -- I provide g as the witness for the existential quantifier (∃ g).
  use g

  -- Now I must prove that g is Bijective (Inj ∧ Surj)
  constructor

  · -- Step 1: Prove that g is Injective
    -- Goal: ∀ y₁ y₂, g y₁ = g y₂ → y₁ = y₂
    intro y₁ y₂ h_g
    -- We can prove this using a calculation block (`calc`), which mimics handwritten math.
    calc
    y₁ = f (g y₁) := (h_fg y₁).symm
    _  = f (g y₂) := by rw [h_g]
    _  = y₂       := (h_fg y₂)

  · -- Step 2 : Prove that g is Surjective
    -- Goal: ∀ x : A, ∃ y : B, g y = x
    intro x
    -- The natural choice for y is f x. I use it:
    use f x
    -- The goal is now: g (f x) = x.
    -- I know that f (g (f x)) = f x (by substituting y with f x in h_fg).
    -- Since f is injective, f(a) = f(b) implies a = b. I apply this rule.
    apply h_inj
    -- Now the goal perfectly matches h_fg
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

  · -- Step 1: Prove that g ∘ f is Injective
    -- Goal: ∀ x₁ x₂, (g ∘ f) x₁ = (g ∘ f) x₂ → x₁ = x₂
    intro x₁ x₂ h_gf
    -- By definition of composition, g(f(x₁)) = g(f(x₂))
    -- Since g is injective f(x₁) = f(x₂)
    have h_f : f x₁ = f x₂ := hg_inj (f x₁) (f x₂) h_gf
    exact hf_inj x₁ x₂ h_f

  · -- Step 2: Prove that g ∘ f is Surjective
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
  *NOTE: The relation =_c is **NOT** an equivalence relation.*
  An equivalence relation must be a subset of a Cartesian product (A × A) of a set A.
  =_c is defined on the class of **ALL SETS** !
-/

-- *======================================================================================================*
-- *PROBLEM 2:*
-- *1. Show that ∀ α, β ∈ ℝ with α < b, [0, 1] =_c [α, β]*

-- In Lean, closed intervals are denoted by `Set.Icc` (Interval Closed Closed).
-- I use `↥` to coerce the Set into a Type so it fits our `=_c` definition.
theorem equinumerous_closed_intervals (α β : ℝ) (h_less : α < β) :
    ↥(Set.Icc α β) =_c ↥(Set.Icc (0 : ℝ) 1) := by

  -- I need to define a function f : [0, 1] → [α, β]
  -- Based on the notes I choose f(x) = (x - α) / (β - α).
  -- Since the inputs and outputs are `Subtypes` (they carry a proof that they belong to the interval)
  -- I must explicitly construct the output with its value and the proof that it falls in [0, 1].
  let f : ↥(Set.Icc α β) → ↥(Set.Icc (0 : ℝ) 1) := fun x =>
    -- `x.eval` is the actual real number. `x.property` contains the proof that α ≤ x.val and x.val ≤ β
    let x_val := x.val
    have hx0 : α ≤ x_val := x.property.1
    have hx1 : x_val ≤ β := x.property.2

    -- Calculate the new value
    let y_val := (x_val - α) / (β - α)

    -- Now I must PROVE that 0 ≤ y_val and y_val ≤ 1 to satisfy the output type [0, 1].
    have h_diff_pos : 0 < β - α := by linarith
    have hy_left : 0 ≤ y_val := by
      apply div_nonneg
      · linarith
      · linarith
    have hy_right : y_val ≤ 1 := by
      rw [div_le_one₀ h_diff_pos]
      linarith

    -- Construct the final Subtype element: ⟨value, ⟨proof_left, proof_right⟩⟩
    ⟨y_val, ⟨hy_left, hy_right⟩⟩

  -- Provide f as the witness for the bijection:
  use f

  -- Now I must prove f is bijective
  constructor
  · -- Prove Injective
    dsimp [Injective]
    intro x₁ x₂ h_eq
    have h_val_eq : (x₁.val - α) / (β - α) = (x₂.val - α) / (β - α) := by
      exact congr_arg Subtype.val h_eq

    have h_nonzero : β - α ≠ 0 := by linarith

    -- Multiply both sides by (β - α)
    have h_mul : (x₁.val - α) / (β - α) *(β - α) = (x₂.val - α) / (β - α) * (β - α) := by
      rw [h_val_eq]

    -- Cancel out
    rw [div_mul_cancel₀ (x₁.val - α) h_nonzero, div_mul_cancel₀ (x₂.val - α) h_nonzero] at h_mul

    -- Now linarith can easily solve x₁.val - α = x₂.val - α
    have h_x_val_eq : x₁.val = x₂.val := by linarith

    exact Subtype.ext h_x_val_eq

  · -- Prove Surjective
    dsimp [Surjective]
    intro y
    let y_val := y.val
    have hy0 : 0 ≤ y_val := y.property.1
    have hy1 : y_val ≤ 1 := y.property.2

    -- The inverse function gives x = α + y * (β - α)
    let x_val := α + y_val * (β - α)

    -- I must prove that x_val is in [α, β]
    have hx_left : α ≤ x_val := by nlinarith
    have hx_right : x_val ≤ β := by nlinarith

    let x : ↥(Set.Icc α β) := ⟨x_val, ⟨hx_left, hx_right⟩⟩
    use x

    -- Prove f(x) = y
    apply Subtype.ext
    have h_nonzero : β - α ≠ 0 := by linarith

    -- I will use this step:
    have h1 : α + y_val * (β - α) - α = y_val * (β - α) := by ring

    -- I show that f(x) = ((α + y * (β - α)) - α) / (β - α) = y
    calc
      (x_val - α) / (β - α) = ((α + y_val * (β - α)) - α) / (β - α) := by rfl
      _                     = (y_val * (β - α)) / (β - α) := by rw [h1]
      _                     = y_val := by rw [mul_div_cancel_right₀ y_val h_nonzero]


-- *2. Prove that (-π/2, π/2) =_c ℝ*

-- Open intervals are denoted by `Set.Ioo` (Interval Open Open).
-- Based on the notes, I use f(x) = x / (π/2 - |x|)
theorem equinumerous_open_real :
    ↥(Set.Ioo (- (Real.pi / 2)) (Real.pi / 2)) =_c ℝ := by

  -- Define f : (-π/2, π/2) → ℝ
  let f : ↥(Set.Ioo (- (Real.pi / 2)) (Real.pi / 2)) → ℝ := fun x =>
    x.val / ((Real.pi / 2) - |x.val|)
  use f
  constructor

  · -- Prove f is injective
    dsimp [Injective]
    intro x₁ x₂ h_eq
    have h_val : x₁.val / (Real.pi / 2 - |x₁.val|) = x₂.val / (Real.pi / 2 - |x₂.val|) := h_eq
    -- Split into 4 cases based on the signs of x₁ and x₂
    by_cases h1_pos : 0 ≤ x₁.val
    · by_cases h2_pos : 0 ≤ x₂.val

      · -- CASE 1: x₁ ≥ 0 and x₂ ≥ 0
        rw [abs_of_nonneg h1_pos, abs_of_nonneg h2_pos] at h_val

        have h_den1_pos : 0 < Real.pi / 2 - x₁.val := by linarith [x₁.property.2]
        have h_den2_pos : 0 < Real.pi / 2 - x₂.val := by linarith [x₂.property.2]

        -- Cross-multiply using `div_eq_div_iff`
        have h_cross : x₁.val * (Real.pi / 2 - x₂.val) = x₂.val * (Real.pi / 2 - x₁.val) := by
          exact (div_eq_div_iff (ne_of_gt h_den1_pos) (ne_of_gt h_den2_pos)).mp h_val

        apply Subtype.ext
        nlinarith

      · -- CASE 2: x₁ ≥ 0 and x₂ < 0
        have h2_neg : x₂.val < 0 := by linarith [h2_pos]
        rw [abs_of_nonneg h1_pos, abs_of_neg h2_neg] at h_val

        -- Clean up the "minus minus" so Lean sees a standard addition
        have h_clean : Real.pi / 2 - -x₂.val = Real.pi / 2 + x₂.val := by ring
        rw [h_clean] at h_val

        have h_den1_pos : 0 < Real.pi / 2 - x₁.val := by linarith [x₁.property.2]
        have h_den2_pos : 0 < Real.pi / 2 + x₂.val := by linarith [x₂.property.1]

        -- Cross-multiply
        have h_cross : x₁.val * (Real.pi / 2 + x₂.val) = x₂.val * (Real.pi / 2 - x₁.val) :=
          (div_eq_div_iff (ne_of_gt h_den1_pos) (ne_of_gt h_den2_pos)).mp h_val

        -- nlinarith sees LHS ≥ 0 (since x₁ ≥ 0) and RHS < 0 (since x₂ < 0) -> Contradiction!
        nlinarith

    · have h1_neg : x₁.val < 0 := by linarith

      by_cases h2_pos : 0 ≤ x₂.val

      · -- CASE 3: x₁ < 0 and x₂ ≥ 0
        rw [abs_of_neg h1_neg, abs_of_nonneg h2_pos] at h_val

        -- Clean up the "minus minus"
        have h_clean : Real.pi / 2 - - x₁.val = Real.pi / 2 + x₁.val := by ring
        rw [h_clean] at h_val

        have h_den1_pos : 0 < Real.pi / 2 + x₁.val := by linarith [x₁.property.1]
        have h_den2_pos : 0 < Real.pi / 2 - x₂.val := by linarith [x₂.property.2]

        -- Cross-multiply
        have h_cross : x₁.val * (Real.pi / 2 - x₂.val) = x₂.val * (Real.pi / 2 + x₁.val) :=
          (div_eq_div_iff (ne_of_gt h_den1_pos) (ne_of_gt h_den2_pos)).mp h_val

        -- Contradiction
        nlinarith

      · -- CASE 4: x₁ < 0 and x₂ < 0
        have h2_neg : x₂.val < 0 := by linarith
        rw [abs_of_neg h1_neg, abs_of_neg h2_neg] at h_val

        have h1_clean : Real.pi / 2 - - x₁.val = Real.pi / 2 + x₁.val := by ring
        have h2_clean : Real.pi / 2 - - x₂.val = Real.pi / 2 + x₂.val := by ring
        rw [h1_clean, h2_clean] at h_val

        have h_den1_pos : 0 < Real.pi / 2 + x₁.val := by linarith [x₁.property.1]
        have h_den2_pos : 0 < Real.pi / 2 + x₂.val := by linarith [x₂.property.1]

        have h_cross : x₁.val * (Real.pi / 2 + x₂.val) = x₂.val * (Real.pi / 2 + x₁.val) :=
          (div_eq_div_iff (ne_of_gt h_den1_pos) (ne_of_gt h_den2_pos)).mp h_val

        apply Subtype.ext
        nlinarith

  · -- Prove f is surjective
    dsimp [Surjective]
    intro y

    -- Basic property: π/2 > 0
    have h_pi_pos : 0 < Real.pi / 2 := by linarith [Real.pi_pos]

    by_cases hy : 0 ≤ y

    · -- CASE 1: y ≥ 0
      let x_val := (y * (Real.pi / 2)) / (1 + y)

      have h_den_pos : 0 < 1 + y := by linarith

      -- I prove that x_val < π/2
      have hx_right : x_val < Real.pi / 2 := by
        -- transform to product: y*(π/2)=(π/2)*(1+y)
        rw [div_lt_iff₀ h_den_pos]
        linarith

      -- I prove that -π/2 < x_val
      have hx_left : - (Real.pi / 2) < x_val := by
        -- x_val ≥ 0, so its obviously > π/2
        have hx_nonneg : 0 ≤ x_val := div_nonneg (by nlinarith) (by linarith)
        linarith

      -- I create the Subtype
      let x : ↥(Set.Ioo (- (Real.pi / 2)) (Real.pi / 2)) := ⟨x_val, ⟨hx_left, hx_right⟩⟩
      use x

      -- I prove f(x)=y
      change x_val / (Real.pi / 2 - |x_val|) = y
      have hx_nonneg : 0 ≤ x_val := div_nonneg (by nlinarith) (by linarith)

      -- Remove | . |
      have h_val : x_val / (Real.pi / 2 - |x_val|) = x_val / (Real.pi / 2 - x_val) := by
        rw [abs_of_nonneg hx_nonneg]
      rw [h_val]

      -- The denominator can be simplified to (π/2)/(1+y)
      have h_den_simp : Real.pi / 2 - x_val = (Real.pi / 2) / (1 + y) := by
        calc
          Real.pi / 2 - x_val
            = Real.pi / 2 - (y * (Real.pi / 2) / (1 + y)) := rfl
          _ = (Real.pi + y * Real.pi - y * Real.pi) / (2 * (1 + y)) := by field_simp
          _ = Real.pi / (2 * (1 + y)) := by ring_nf
          _ = (Real.pi / 2) / (1 + y) := by field_simp

      rw [h_den_simp]
      -- Simplify denominators (creates 2 goals)
      rw [div_div_div_cancel_right₀]
      · -- Goal 1: the equation that is left:
        rw [mul_div_cancel_right₀ y (ne_of_gt h_pi_pos)]
      · -- Goal 2: The proof that 1 + y ≠ 0 (so it cancels out):
        linarith

    · -- CASE 2: y < 0
      have hy_neg : y < 0 := by linarith

      let x_val := (y * (Real.pi / 2)) / (1 - y)

      have h_den_pos : 0 < 1 - y := by linarith

      -- I prove that -π/2 < x_val
      have hx_left : - (Real.pi / 2) < x_val := by
        have h_lt : - (Real.pi / 2) * (1 - y) < y * (Real.pi / 2) := by nlinarith
        exact (lt_div_iff₀ h_den_pos).mpr h_lt

      -- I prove that x_val < π/2
      have hx_right : x_val < Real.pi / 2 := by
        have h_num_neg : y * (Real.pi / 2) < 0 := by nlinarith
        have hx_neg : x_val < 0 := div_neg_of_neg_of_pos h_num_neg h_den_pos
        linarith

      -- I create the Subtype
      let x : ↥(Set.Ioo (- (Real.pi / 2)) (Real.pi / 2)) := ⟨x_val, ⟨hx_left, hx_right⟩⟩
      use x

      -- I prove f(x) = y
      change x_val / (Real.pi / 2 - |x_val|) = y

      -- Since y < 0, I also have that x_val < 0
      have h_num_neg : y * (Real.pi / 2) < 0 := by nlinarith
      have hx_neg : x_val < 0 := div_neg_of_neg_of_pos h_num_neg h_den_pos

      -- Now I can remove the | . |
      have h_val : x_val / (Real.pi / 2 - |x_val|) = x_val / (Real.pi / 2 + x_val) := by
        have h_abs : |x_val| = - x_val := abs_of_neg hx_neg
        rw [h_abs]
        ring

      rw [h_val]

      -- The denominator can be simplified to (π/2)/(1-y)
      have h_den_simp : Real.pi / 2 + x_val = (Real.pi / 2) / (1 - y) := by
        calc
          Real.pi / 2 + x_val = Real.pi / 2 + (y * (Real.pi / 2) / (1 - y)) := rfl
          _                   = (Real.pi - Real.pi * y + Real.pi * y) / (2 * (1 - y)) := by field_simp
          _                   = Real.pi / (2 * (1 - y)) := by ring
          _                   = (Real.pi / 2) / (1 - y) := by field_simp

      rw [h_den_simp]

      -- Simplify denominators (rewrites the goal and creates a new one: Prove that 1 - y ≠ 0)
      rw [div_div_div_cancel_right₀]

      · -- Goal 1: Solve equation
        rw [mul_div_cancel_right₀ y (ne_of_gt h_pi_pos)]
      · -- Goal 2: 1 - y ≠ 0
        linarith

-- *======================================================================================================*
-- *PROBLEM 4:*
-- *Show that for every set A, |P(A)| = 2^(|A|)*
-- Equivalently, I need to prove that the powerset of A (`Set A`) is equinumerous to the set of functions
-- from A to a 2-element set (for example Bool: true/false)

theorem powerset_equinumerous_two_pow (A : Type) : Set A =_c (A → Bool) := by

  -- Use `Classical Logic` only for this proof:
  classical

  -- I define the mapping `F` that takes a subset S ⊆ A and returns its
  -- characteristic function (indicator function):
  let F : Set A → (A → Bool) := fun S =>
    fun a => if a ∈ S then true else false

  use F
  constructor

  · -- Step 1: Prove Injective
    dsimp [Injective]
    intro S₁ S₂

    -- Transform the goal from (F S₁ = F S₂ → S₁ = S₂) to (S₁ ≠ S₂ → F S₁ ≠ F S₂)
    contrapose!

    -- Assume the sets are not equal (h_neq)
    -- and then I want to prove F S1 ≠ F S2. Towards contradiction (assume h_eq):
    intro h_neq h_eq



    -- Since S1 ≠ S2, there must exist an element `a` that belongs to one set but not the other
    have h_diff : ∃ a, (a ∈ S₁ ∧ a ∉ S₂) ∨ (a ∉ S₁ ∧ a ∈ S₂) := by
      by_contra h_all
      push Not at h_all
      apply h_neq
      ext x
      -- Apply `h_all` to `x`:
      have hx := h_all x

      constructor
      · -- x ∈ S₁ → x ∈ S₂
        exact hx.left
      · -- x ∈ S₂ → x ∈ S₁
        intro h2
        -- Suppose the opposite (x ∉ S₁)
        by_contra h1
        have h_not_in_S2 := hx.right h1
        contradiction


    -- Ι extract `a` amd the OR contradiction
    rcases h_diff with ⟨a, h_or⟩
    have h_fun := congr_fun h_eq a

    -- I unfold F explicitly to expose the if-then-else structure to the rewrite tactic
    change (if a ∈ S₁ then true else false) = (if a ∈ S₂ then true else false) at h_fun

    -- Split into the 2 symmetric `WLOG` cases
    rcases h_or with ⟨h_in1, h_notin2⟩ | ⟨h_notin1, h_in2⟩
    · -- Case 1: a ∈ S₁ and a ∉ S₂
      rw [if_pos h_in1, if_neg h_notin2] at h_fun
      contradiction
    · -- Case 2: a ∉ S₁ and a ∈ S₂
      rw [if_neg h_notin1, if_pos h_in2] at h_fun
      contradiction

  · -- Step 2: Prove Surjective
    dsimp [Surjective]
    intro f

    -- I construct the pre-image set S: the set of all elements `a` where f(a) = true (= 1)
    let S : Set A := { a : A | f a = true }
    use S

    -- To prove two functions are equal, I must show their outputs are equal for all inputs.
    ext a

    -- Unfold F
    dsimp [F]

    -- Since f(a) is a boolean, it has exactly two possible values: false or true.
    cases h : f a

    · -- Case 1: f(a) = false
      -- An element belongs to S only if f(a) = true.
      have h_not_in : a ∉ S := by
        change ¬(f a = true)
        rw [h]
        simp

      -- Since a ∉ S, the if statement evaluates to false
      rw [if_neg h_not_in]

    · -- Case 2 : f(a) = true
      have h_in : a ∈ S := by
        change (f a = true)
        exact h

      -- Since a ∈ S, the if statement evalutates to true
      rw [if_pos h_in]

-- *=====================================================================================================*
-- *PROBLEM 5:*
-- *Show that for sets A, B, C, (|A|^|B|)^|C| = |A|^(|B|·|C|)*

theorem power_power_equinumerous (A B C : Type) : (C → B → A) =_c (C × B → A) := by

  -- I define the mapping F (on the notes π(.))
  -- It takes a function `q : C → B → A` and returns a function that takes a pair `(x, y) : C × B`.
  let F : (C → B → A) → (C × B → A) := fun q =>
    fun (x, y) => q x y

  use F

  constructor

  · -- Step 1: Prove Injective
    dsimp [Injective]
    intro q₁ q₂ h_eq

    -- To prove that two functions q₁ and q₂ are equal, I must show
    -- that they return the same value for all possible inputs c and b.
    -- The `ext` tactic applies function extensionality for both arguments.
    ext c b

    have h_val := congr_fun h_eq (c, b)

    exact h_val

  · -- Step 2: Prove Surjective
    dsimp [Surjective]
    intro p

    -- I must construct the pre-image of p : `q : C → B → A`
    let q : C → B → A := fun c b => p (c, b)
    use q
