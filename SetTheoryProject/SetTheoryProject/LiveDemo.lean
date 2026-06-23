import Mathlib.Tactic
set_option linter.style.whitespace false

-- 1ος τρόπος: Tactic Mode
example {p q : Prop} : (p → q) → (¬q → ¬p) := by
  sorry

-- 2ος τρόπος: Term Mode
example {p q : Prop} : (p → q) → (¬q → ¬p) :=
  sorry
