/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 3 * 5 ≤ 3*k := by rel [h5]
          _ = 13 := by rw [hk]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h -- suppose there WAS a natural number n s.t. n^2 = 2
  obtain ⟨n, hn⟩ := h --get a witness
  obtain h1 | h2 := le_or_succ_le n 1 -- n ≤ 1 or 2 ≤ n
  · have H : 2 ≤  1 := by
      --have hn_rev : 2=n^2:= by
       --  symm
       --  apply hn


      calc 2 = n^2 := by symm
                         apply hn
              _ ≤ 1^2 := by rel [h1]
               _ = 1 := by numbers
    numbers at H
  · have H : 4 ≤ 2 := by
      calc 4 = 2^2 := by numbers
          _ ≤ n^2 := by rel [h2]
          _ = 2 := by rw [ hn]
    numbers at H


example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro hn_odd
    intro hn_even
    rw [Int.even_iff_modEq] at hn_even
    rw [Int.odd_iff_modEq] at hn_odd
    have H : 0 ≡ 1 [ZMOD 2] := by
      calc
        0 ≡ n [ZMOD 2] := by rel [hn_even]
        _ ≡ 1 [ZMOD 2] := by apply hn_odd
    numbers at H
  · intro hn_neg_even
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) ≡ 1 + 3*1 [ZMOD 3] := by extra
      _ ≡ 2^2 [ZMOD 3] := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  sorry

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · sorry
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · sorry
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, ht⟩ := h
  have :=
    calc 5 ≤ t := ht.right
        _ ≤ 4 := ht.left
  numbers at this


example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨a, ha⟩ := h
  sorry

example : ¬ Int.Even 7 := by
  intro h
  rw [Int.even_iff_modEq] at h
  have h' : 7 ≡ 1 [ZMOD 2] := by
    use 3
    numbers
  have :=
    calc
      0 ≡ 7 [ZMOD 2] := by
        symm at h
        apply h
      _ ≡ 1 [ZMOD 2] := h'
  numbers at this

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have hn4 : n = 4 := by addarith [hn]
  have hn4' : 4 = n := by
    symm at hn4
    apply hn4
  have :=
    calc
      (16:ℤ ) = 4^2 := by numbers
      _ = n^2 := by rw [hn4]
      _ = 10 := by rw [h2]
  numbers at this

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h
  obtain h|h := h
  · have h' : 3 ≤ -x := by addarith [h]
    have hx' := calc
      9 = (3)^2 := by numbers
      _ ≤ (-x)^2 := by rel [h']
      _ = x^2 := by ring
    have :=
      calc 9 ≤ x^2 := hx'
          _  < 9 := hx
    numbers at this
  · have h' : x^2 ≥ 9 := calc
      x^2 ≥ 3^2 := by rel [h]
      _ = 9 := by numbers
    have := calc
      9 ≤ x^2 := h'
      _ < 9 := hx
    numbers at this


example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ⟨n, hk⟩ := h
  have hnplus1_gt_n : n+1 > n := by extra
  have h_nplus1_even : Nat.Even (n+1) := by apply hk (n+1) hnplus1_gt_n
  obtain h'|h' := Nat.even_or_odd (n)
  · have h_nplus1_odd : Nat.Odd (n+1) := by
      obtain ⟨c, hc⟩ := h'
      dsimp [Nat.Odd]
      use c
      rw [hc]
    obtain ⟨c, hc⟩ := h_nplus1_even
    obtain ⟨d, hd⟩ := h_nplus1_odd
    obtain hc'|hd' := le_or_lt c d
    · have he := calc
        2*c ≤ 2*d := by rel [hc']
        _  < 2*d + 1 := by extra
      have := calc
        n+1 = 2*c := by apply hc
        _ < 2*d + 1 := by apply he
        _ = n + 1 := by rw [hd]
      have h1 : 1 < 1 := by addarith [this]
      numbers at h1
    · sorry

  · sorry



example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  --dsimp [Int.ModEq] at h
  obtain ⟨c, hc⟩ := h
  sorry

example : ¬ Prime 1 := by
  intro h
  dsimp [Prime] at h
  obtain ⟨h1, h2⟩ := h
  numbers at h1

example : Prime 97 := by
  sorry
