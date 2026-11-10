/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ⟨h1,h2⟩ | h := h
    constructor
    · apply h1
    · left
      apply h2
    · constructor
      · apply h.left
      · right
        apply h.right



#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  left
  apply h.left

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1 h3
  · apply h2 h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨h1, h2⟩:=h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  obtain ⟨h1,h1'⟩:= h1
  intro h
  apply h1 at h
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain h|h := h1
  · apply h
  · apply h2
    apply h


example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨h1,h2⟩:= h
  constructor
  · intro h
    constructor
    · apply h1 h.left
    · apply h.right
  · intro h
    constructor
    · apply h2 h.left
    · apply h.right


example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro h
    apply h.left
  · intro h
    constructor <;> apply h


example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor <;> {
    intro h
    obtain h|h:= h
    · right
      apply h
    · left
      apply h
  }

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · sorry
    · sorry
  · intro h
    intro hneg
    obtain e|f := hneg
    · have := h.left
      contradiction
    · have := h.right
      contradiction



example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro h
  apply h1
  apply h2


example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h2
    obtain ⟨x, hx⟩ := h2
    specialize h x
    use x
    obtain ⟨ hp, hq ⟩ := h
    apply hp hx
  · intro h2
    obtain ⟨x, hx⟩ := h2
    specialize h x
    use x
    obtain ⟨ hp, hq ⟩ := h
    apply hq hx



example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor <;> {
    intro h
    obtain ⟨x, hx⟩ := h
    obtain ⟨ y, hy⟩ := hx
    use y
    use x
    apply hy
  }

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h y x
    specialize h x y
    apply h
  · intro h x y
    specialize h y x
    apply h


example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    --apply h -- ahh, if only...
    obtain ⟨hx, q⟩ := h
    obtain ⟨x, hx⟩:= hx
    use x
    constructor
    · apply hx
    · apply q
  · intro h
    obtain ⟨x, h, q⟩ := h
    constructor
    · use x
      apply h
    · apply q
