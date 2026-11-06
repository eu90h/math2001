/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Odd]
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Even]
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  have h1 : x^2 + x - 6 = (x+3)*(x-2) := by ring
  constructor
  · intro h2
    rw [h1] at h2
    apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
    obtain hx|hx := h2
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h2
    rw [h1]
    obtain hx|hx := h2
    · calc
        (x + 3) * (x - 2) = (-3 + 3) * (-3 - 2) := by rw [hx]
        --_ = 0 * -5 := by numbers
        _ = 0 := by numbers
    · calc
        (x + 3) * (x - 2) = (2 + 3) * (2 - 2) := by rw [hx]
        --_ = 5 * 0 := by numbers
        _ = 0 := by numbers


example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    --calc
    --  (2*a - 5)^2 = 4*(a^2 - 5*a + 5) + 5 := by ring
    --  _ ≤ 4 * -1 + 5 := by rel [h]
    --  _ = 1^2 := by numbers
    sorry
  · intro ha
    obtain ha|ha := ha
    · rw [ha]
      numbers
    · rw [ha]
      numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn2|hn2 := hn2
  · have h3 : n = 4 := by addarith [hn2]
    use 2
    --exact h3 --this works too
    apply h3
  · have h3 : n = 6 := by addarith [hn2]
    use 3
    --exact h3
    apply h3

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn1|hn1 := hn1
  · have h : n = 4 := by addarith [hn1]
    use 2
    exact h
  · have h : n = 6 := by addarith [hn1]
    use 3
    exact h

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra -- 2*1 is a neutral qty under the relation "congruence modulo 2"


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have h2 : 2*x = 12 := by addarith [h]
    sorry
  · intro h
    rw [h]
    numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    have h1 : (7:ℤ) ∣ 63 := by
      use 9
      numbers
    have h2 : (9:ℤ) ∣ 63 := by
      use 7
      numbers
    dsimp [(· ∣ ·)] at *
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := h1
    obtain ⟨c, hc⟩ := h2
    constructor
    · use b * a
      rw [hb] at ha
      calc
        n = 7 * b * a := by apply ha
        _ = 7 * (b * a) := by ring
    · use c * a
      rw [hc] at ha
      calc
        n = 9 * c * a := by apply ha
        _ = 9 * (c * a) := by ring
  · intro h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    have h1 : 9 ∣ a := by
      rw [ha] at hb
      sorry
    sorry


theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h
    use b
    calc
      a - 0 = a := by ring
      _ = n * b := by apply hb
  · intro h
    obtain ⟨b, hb⟩ := h
    use b
    calc
      a = a - 0 := by ring
      _ = n * b := by apply hb

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨c, hbac⟩ := hab
  have h1 : ∀r, a∣ r*b  := by
    intro r
    use r * c
    rw [hbac]
    ring
  have h2 : ∀r, a ∣ r*b^2 := by
    intro r
    use r*a*c^2
    calc
      r*b^2 = r*(a*c)^2 := by rw [hbac]
      _     = r*a^2*c^2 := by ring
      _     = r*a*(a*c^2) := by ring
      _     = a*(r*a*c^2) := by ring
  have h3 : ∀r, a ∣ r*b^3 := by
    intro r
    use r*a^2*c^3
    calc
      r*b^3 = r*(a*c)^3 := by rw [hbac]
      _     = r*a^3*c^3 := by ring
      _     = r*a*(a^2*c^3) := by ring
      _     = a * (r*a^2*c^3) := by ring
  have h1' : a ∣ 3*b := by apply h1
  have h2' : a ∣ -1*b^2 := by apply h2
  have h3' : a ∣ 2*b^3 := by apply h3
  --question: is something like the following possible?
  --obtain ⟨⟨d1, hd1⟩, ⟨d1, hd1⟩, ⟨d1, hd1⟩⟩ := ⟨h1', h2', h3'⟩
  obtain ⟨d1, hd1⟩ := h1'
  obtain ⟨d2, hd2⟩ := h2'
  obtain ⟨d3, hd3⟩ := h3'
  use d1 + d2 + d3
  calc
    2*b^3 - b^2 + 3*b = 2*b^3 + -1*b^2 +3*b := by ring
    _ = a*d3 + -1*b^2 +3*b := by rw [hd3]
    _ = a*d3 + a*d2 +3*b := by rw [hd2]
    _ = a*d3 + a*d2 +a * d1 := by rw [hd1]
    _ = a*(d1+d2+d3) := by ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    --k cant be 3 because then k^2 = 9 > 6
    sorry
  · intro h
    obtain h|h|h := h
    · calc
        k^2 = 0^2 := by rw [h]
        _ = 0 := by ring
        _ ≤ 6 := by numbers
    · calc
        k^2 = 1^2 := by rw [h]
        _ = 1 := by ring
        _ ≤ 6 := by numbers
    · calc
        k^2 = 2^2 := by rw [h]
        _ = 4 := by numbers
        _ ≤ 6 := by numbers
