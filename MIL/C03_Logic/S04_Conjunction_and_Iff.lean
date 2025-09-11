import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')


/-~ A gradual descent from term-stype to tactic-style ~-/
example {m n : ℕ} : (m ∣ n ∧ m ≠ n) → m ∣ n ∧ ¬n ∣ m := -- pure term
  fun ⟨h₀, h₁⟩ ↦ ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `rcases` with term
  match h with
    | ⟨h₀, h₁⟩ => exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `cases ⋯ with |`
  cases h with
  | intro h₀ h₁ =>
    exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `cases ⋯ ; case`
  cases h; case
    intro h₀ h₁ =>
    exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `cases ⋯ ; next`
  cases h;  -- `next` is just `case` with `intro`
  next h₀ h₁ =>
    exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `rcases` with term
  rcases h with ⟨h₀, h₁⟩ -- `h` discarded
  exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `rcases`
  rcases h with ⟨h₀, h₁⟩; constructor
  · assumption
  · contrapose! h₁
    exact Nat.dvd_antisymm h₀ h₁
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `have`
  have ⟨h₀, h₁⟩ := h -- `h` remain available
  exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- `obtain`
  obtain ⟨h₀, h₁⟩ := h -- `h` discarded
  exact ⟨h₀, fun h' ↦ h₁ (Nat.dvd_antisymm h₀ h')⟩
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by -- navi
  have ⟨_, right⟩ := h -- `h` remain available
  constructor
  · exact h.left
  · contrapose! right
    exact Nat.dvd_antisymm h.left right

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor; repeat
  · rintro ⟨h₀, h₁⟩
    use h₀
    contrapose! h₁
    linarith

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    linarith [sq_nonneg x, sq_nonneg y]
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h₀ : x = 0 := aux h
    have h₁ : y = 0 := @aux y x (by linarith)
    exact ⟨h₀, h₁⟩
  · rintro ⟨h₀, h₁⟩
    exact h₀.symm ▸ h₁.symm ▸ by norm_num

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff] at ⊢
  use 0, 1
  constructor <;> norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor; repeat
  · rintro ⟨h₀, h₁⟩
    use h₀
    contrapose! h₁
    first | exact le_of_eq h₁.symm
          | exact le_antisymm h₀ h₁

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  exact fun ⟨h₀, h₁⟩ ↦ h₁ (le_refl a)

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  rintro ⟨hab, hab'⟩ ⟨hbc, hbc'⟩
  constructor
  · exact le_trans hab hbc
  · contrapose! hbc'
    exact le_trans hbc' hab

end
