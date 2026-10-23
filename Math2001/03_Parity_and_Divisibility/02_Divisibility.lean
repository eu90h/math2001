/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [(· ∣ ·)]
  use -3
  numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  rw [hj, hk]
  dsimp [(· ∣ ·)]
  use k^2*j
  ring

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  dsimp [(· ∣ ·)]
  obtain ⟨k, hk⟩ := h
  rw [hk]
  use y*k
  ring

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk⟩ := hab
  have h1 : 0 < a * k := by
    rw [hk] at hb
    exact hb
  cancel k at h1


/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  use 0
  ring

example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · numbers
  · numbers

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  dsimp [(· ∣ ·)]
  rw [hk]
  use k*(3-4*x*k)
  ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk⟩ := h
  dsimp [(· ∣ ·)]
  rw [hk]
  use k*(2*(m*k)^2 + 1)
  ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  dsimp [(· ∣ ·)]
  rw [hk]
  use 2*a^2*k^3 -a*k^2 + 3*k
  ring

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨j, hj⟩ := h2
  dsimp [(· ∣ ·)]
  rw [hp] at hj
  rw [hj]
  use p^3*j
  ring


example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨k, hk⟩ := hpq
  obtain ⟨j, hj⟩ := hqr
  dsimp [(· ∣ ·)]
  rw [hk] at hj
  rw [hj]
  use k^2*j
  ring

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  dsimp [(· ∣ ·)]
  sorry

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  dsimp [(· ∣ ·)]
  sorry
