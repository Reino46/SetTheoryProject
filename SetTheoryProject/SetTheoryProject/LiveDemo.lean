import Mathlib.Tactic
set_option linter.style.whitespace false

-- 1ος τρόπος: Tactic Mode
example {p q : Prop} : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  have hq : q := hpq hp
  contradiction

-- 2ος τρόπος: Term Mode
example {p q : Prop} : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q =>
    fun hnq : ¬q =>
      fun hp : p =>
        show False from hnq (hpq hp)
