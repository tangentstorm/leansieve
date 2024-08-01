import Mathlib.Tactic

example {a b : ℤ} (h1 : a^2 + b^2 = c^2) : 0 ≤ c^2 - a^2 :=
  calc
    0 = c^2 - a^2 - b^2 := by omega
    _ ≤ c^2 - a^2 := by
      have : 0 ≤ b^2 := by exact sq_nonneg b
      omega


example {a b : ℤ} (h1 : c^2 = a^2 + b^2) : c^2 ≥ a^2 := by
  calc c^2
    _ = a^2 + b^2  := h1
    _ ≥ a^2        := Int.le_add_of_nonneg_right (sq_nonneg b)
