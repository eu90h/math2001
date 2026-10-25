/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨k, hk⟩ := hn
  dsimp [(· ∣ · )]
  use 5*k - 3 * n
  calc
    n = 5*(5*n) - 24*n := by ring
    _ = 5*(8*k) - 24*n := by rw [hk]
    _ = 8*(5*k - 3*n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨k, hk⟩ := h1
  dsimp [(· ∣ · )]
  use 2*k - n
  calc
    n = 2*(3*n) - 5*n := by ring
    _ = 2*(5*k) - 5*n := by rw [hk]
    _ = 5*(2*k- n) := by ring


example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  dsimp [(· ∣ · )]
  use 2*n - a
  calc -- -11 + 2*6 = 1
    n = 2*(6*n) - 11*n := by ring
    _ = 2*(6*n) - 6*a := by rw [ha]
    _ = 6*(2*n - a) := by ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨b, hb⟩ := ha
  dsimp [(· ∣ · )]
  -- 5*3 - 2*7 = 1
  use (3*b - 2*a)
  calc
    a = 3*(5*a) - 2*7*a := by ring
    _ = 3*(7*b) - 2*7*a := by rw [hb]
    _ = 7*(3*b - 2*a) := by ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  sorry

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  sorry
