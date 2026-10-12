/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn

  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers

  · apply ne_of_gt
    calc
      2 < 2^2 := by numbers
      _ ≤ n^2 := by rel [hn]


example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1

  obtain hn | hn := h2
  · left
    addarith [hn]
  · right
    addarith [hn]

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hn | hn := h
  · rw [hn]
    numbers
  · rw [hn]
    numbers

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hn | hn := h
  · rw [hn]
    numbers
  · rw [hn]
    numbers

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain hn | hn := h
  · rw [hn]
    numbers
  · rw [hn]
    numbers

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hn | hn := h
  · rw [hn]
    ring
  · rw [hn]
    ring

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  rw [h]
  left
  ring


example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  addarith [h]

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  have h2 : 2*x < 2*x + 1 := by extra
  rw [← h] at h2
  left
  addarith [h2]

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h : (x+3)*(x-1) = x ^ 2 + 2 * x - 3 := by
    calc
      (x+3)*(x-1) = (x+3)*x - (x+3)*1 := by ring
      _ = x*x + 3*x - x*1 - 3*1 := by ring
      _= x^2 +2*x -3 := by ring
  rw [← h] at hx
  apply eq_zero_or_eq_zero_of_mul_eq_zero at hx
  obtain hn0 | hn0 := hx
  · left
    addarith [hn0]
  · right
    addarith [hn0]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  --notice the given polynomial in hab is "almost" like a nice factorization,
  --so let's take the nice part and the bad part separately
  have h : a^2 + 2*b^2 -3*a*b = (a-b)*(a-2*b) := by
    calc
    a^2 + 2*b^2 -3*a*b = a^2 -2*a*b + b^2 + b^2 -a*b := by ring
    _ = (a-b)^2 - b*(a-b) := by ring
    _ = (a-b)*((a-b) - b) := by ring
    _ = (a-b)*(a-2*b) := by ring
  have h2 : a^2 + 2*b^2 -3*a*b = 0 := by addarith [hab]
  rw [h2] at h
  symm at h --we could've flipped the equality in h and proved it that way to save us from symm, but i'm too tired
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  obtain hn0 | hn0 := h
  · left
    addarith [hn0]
  · right
    addarith [hn0]

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h : t^3 - t^2 = 0 := by addarith [ht]
  have h2 : t^3 - t^2 = t^2*(t-1) := by ring
  rw [h2] at h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  obtain hn0 | hn0 := h
  · right
    have h3 : t^2 = t*t := by ring
    rw [h3] at hn0
    apply eq_zero_or_eq_zero_of_mul_eq_zero at hn0
    obtain hn1 | hn1 := hn0
    · exact hn1
    · exact hn1
  · left
    addarith [hn0]

example {n : ℕ} : n ^ 2 ≠ 7 := by
  --we're working over ℕ so it can't be 7 because n would be between 2 and 3.
  have hn := le_or_succ_le n 2
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n^2 = n*n := by ring
      _ ≤ 2*2 := by rel [hn]
      _ = 4 := by rfl
      _ < 7 := by numbers
  · apply ne_of_gt
    calc
      7 < 9 := by numbers
      _ = 3*3 := by rfl
      _ ≤ n*n := by rel [hn]
      _ = n^2 := by ring

example {x : ℤ} : 2 * x ≠ 3 := by
  have hn := le_or_succ_le x 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      2*x ≤ 2*1 := by rel [hn]
      _ = 2 := by numbers
      _ < 2 + 1 := by extra
      _ = 3 := by numbers
  · apply ne_of_gt
    change 2 ≤ x at hn
    calc
      3 < 4 := by numbers
      _ = (2 * 2 : ℤ) := by numbers --typecast to integers
      _ ≤ 2 * x := by rel [hn]

example {t : ℤ} : 5 * t ≠ 18 := by
  have hn := le_or_succ_le t 3
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      5*t ≤ 5*3 := by rel [hn]
      _ = 15 := by numbers
      _ < 18 := by numbers
  · apply ne_of_gt
    calc
      18 < 20 := by numbers
      _ = (5*4 : ℤ) := by numbers
      _ ≤ 5*t := by rel [hn]

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
