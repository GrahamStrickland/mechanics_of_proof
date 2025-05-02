import Mathlib.Data.Real.Basic
import Library.Basic

example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring
