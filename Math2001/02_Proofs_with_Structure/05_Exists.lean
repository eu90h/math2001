/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hx' : -x ≤  0 := by addarith [hx]
    have hxt' : 0 <  x*(-t) := by
      calc
        0 < (-x)*t := by addarith [hxt]
        _ = x*(-t) := by ring
    cancel x at hxt'
    apply ne_of_lt
    have ht : t < 0 := by addarith [hxt']
    exact ht --apply ht works too


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6 --choice for m
  use 5 --choice for n
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc
      p = (p+p)/2 := by ring
      _ < (p+q)/2 := by rel [h]
  · calc
      (p+q)/2 < (q+q)/2 := by rel [h]
      _       = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  --85 is close to 9^2 so lets subtract 4=2^2
  use 9
  use 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  --any negative number whose abs. value is less than 1 works.
  use -0.1
  constructor
  · numbers
  · numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0
  use 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  --if x is < 0 then it is easy because any square is nonnegative
  --if x > 0 then just try y = x+1
  obtain h1|h1 := le_or_gt x 0
  · use 0.1
    calc
      x ≤ 0 := by exact h1
      _ < 0.1^2 := by numbers
  · use x+1
    have h2 : x^2 > 0 := by extra
    have h3 : 2*x > 0 := by extra
    calc
      x < x^2 + x + x + 1 := by addarith [h1, h2]
      _ = (x + 1)^2 := by ring


example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have ha' : 1 < a + t - a * t := by addarith [ha]
  have H := le_or_gt t 1
  obtain h1|h1 := H
  · have h2 : t <  t + a*(1-t) := by
      calc
        t ≤ 1 := by exact h1
        _ < a + t - a*t := by exact ha'
        _ = t + a*(1-t) := by ring
    have h3 : 0 < a*(1-t) := by addarith [h2]
    have h5: 0 ≤ 1-t := by addarith [h1]
    have h4: 0 < a := by cancel (1-t) at h3
    have h6 : 0 ≤ a*(1-t) := by rel [h3, h4]
    have h7 : t < 1 := by {cancel a at h3;addarith [h3]}
    apply ne_of_gt at h7
    symm at h7
    exact h7
  · --apply ne_of_gt
    --exact h1
    exact ne_of_gt h1

--example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
--  obtain ⟨a, ha⟩ := h
--  intro ht
--  rw [ht] at ha
--  tauto

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  rw [← ha]
  --5/2 ∉ ℤ
  --have hn := le_or_succ_le a 2
  obtain h1|h1 := le_or_succ_le a 2
  · apply ne_of_lt
    --have h1' : 2*a ≤ 4 := by
    calc
      2 * a ≤ 2*2 := by rel [h1]
      _     = 4   := by numbers
      _     < 5   := by numbers
  · apply ne_of_gt
    calc
      5 < 6 := by numbers
      _ = (2*3 : ℤ) := by numbers --typecast to ints
      _ ≤ 2*a := by rel [h1]


example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  --inequality flips on sign of n
  obtain h1|h1 := le_or_gt n 0
  --n ≤ 0 → a*n ≤ 0 so a*n + 7 ≤ 7
  · use (1234567890 : ℤ)
    calc
      2 * 1234567890^3 ≥ 7 := by numbers
      _ = (0 * 1234567890:ℤ ) + 7 := by numbers
      _ ≥ n * 1234567890 + 7 := by rel [h1]
  · sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
