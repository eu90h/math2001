/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  intro y hy_geq1 hy_leq3
  have h  : y-2 ≥ -1 := by addarith [hy_geq1]
  have h' : y - 2 ≤ 1 := by addarith [hy_leq3]
  have h2 : y^2 ≤ 9 := by
    calc
      y^2 ≤ 3^2 := by rel [hy_leq3]
      _ = 9 := by numbers
  have h4 : 0 ≤ y - 1 := by addarith [hy_geq1]
  have h3 : y * (y - 1) ≤ 3 * (y - 1) := by rel [hy_leq3, h4]
  sorry
  intro y hy

  sorry

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  · intro y hy
    have h2 : 4*y = 12 := by addarith [hy]
    calc
      y = 4*y / 4 := by ring
      _ = 12 /4 := by rw [h2]
      _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro a
    extra
  · intro a ha
    apply Nat.le_antisymm
    · apply ha
    · extra

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    · numbers
    · constructor
      · numbers
      · use 3
        numbers
  · intro y hy
    obtain ⟨ h1, h2, h3⟩  := hy
    obtain ⟨a, ha ⟩ := h3
    --using the two bounds h1 and h2 together with h1
    --we end up with the bound
    --      9 ≤ 11 - y ≤ 11
    --which implies y = 0, y = 1 or y = 2
    --but since ha implies 3 | 11 - y, then y = 2
    have h3 : 9 ≤ 11 - y := by addarith [h2]
    have h1' : 0 ≥ -y := by addarith [h1]
    have h4 : 11 - y ≤ 11 := by addarith [h1']
    --we just have to show that the only multiple of 3 in [9, 11] is 9.
    sorry
