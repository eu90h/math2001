/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    0 < 1 := by numbers
    _ ≤  y^2 + 1 := by extra

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra


/-! # Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have h : m =4 := by
    addarith [hm]
  have m_nonneg : m > 0 := by
    calc
      0 < 4 := by numbers
      _ = m := by rw [h]
  calc
    6 < 12 := by numbers
    _ = (3 * 4 : ℤ) := by numbers
    _ = 3 * m := by rw [← h]


example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  -- first thought: notice we can subtract h2 from h1 to get 3s -2s = s  ≤  -6 + 4 = 2
  -- but we need to prove the other inequality s ≥ 2 in order to force the equality
  apply le_antisymm -- this is precisely the needed condition
  · calc
      s = 3*s - 2*s := by ring
      _ ≤ -6 - -4 := by rel [h1, h2]
      _  = -2 := by numbers
  · calc -- notice that h2 is precisely twice our goal.
      -2 = -4/2 := by numbers
      _ ≤ 2*s/2 := by rel [h2]
      _ = s := by ring
