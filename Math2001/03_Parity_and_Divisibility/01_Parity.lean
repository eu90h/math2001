/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at hn
  obtain ⟨r, hr⟩ := hn
  dsimp [Odd]
  use 7*r + 1
  rw [hr]
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw [ha, hb]
  dsimp [Odd]
  use (2*b*(a+1) + b + (a+1))
  --calc
  --  (2*a+1)*(2*b+1) + 2 * (2*b+1) = (2*b+1) * (2*a + 3) := by ring
  --  _ = (2*b+1) * (2*(a+1) + 1) := by ring
  --  _ = 4*(a*b+b)+2*b+2*(a+1)+1 := by ring
  --  _ = 2*(2*b*(a+1)+b+(a+1)) + 1 := by ring
  --or just...
  ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨k, hk⟩ := hm
  dsimp [Even]
  rw [hk]
  use 3*k - 1
  ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Odd]
  obtain ⟨k, hk⟩ := hn
  sorry


example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  numbers

example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hj⟩ := hn
  use i + j
  rw [hi, hj]
  ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  rw [hi, hj]
  use i - j - 2
  ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  rw [hi, hj]
  use 3*i + j - 1
  ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, hj⟩ := hs
  --6i + 3 - 10j - 5 = 2(3i - 5j - 1)
  use 3*i - 5*j -1
  rw [hi, hj]
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hx
  rw [hi]
  --2^3 i^3 + 3 * 2^2 * i^2 + 3*2 * i + 1
  use 4 * i^3 + 3 * 2*i^2  + 3*i
  ring


example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hn
  rw [hi]
  --          + 2
  --4i^2 + 4i + 1
  --      -6i - 3
  --4i^2  -2i
  use 2*i^2 - i
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := ha
  rw [hi]
  --4i^2 + 4i + 1
  --     + 4i + 2
  --          - 4
  --4i^2 + 8i - 1
  --2(2i^2 + 4i - 1) + 1
  use 2*i^2 + 4*i - 1
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hp
  rw [hi]
   --4i^2 + 4i  + 1
   --     + 6i  + 3
   --           - 5
   --4i^2 + 10i - 1
  use 2*i^2 + 5*i - 1
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Even, Odd] at *
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  rw [hi, hj]
  --4ij + 2i + 2j + 1
  use 2*i*j + (i+j)
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  dsimp [Even, Odd] at *
  sorry

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp [Even, Odd] at *
  sorry

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  dsimp [Even, Odd] at *
  sorry
