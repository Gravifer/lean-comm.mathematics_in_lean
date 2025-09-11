import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x with
  | inl h => exact le_of_eq (abs_of_nonneg h).symm
  | inr h => linarith [abs_of_neg h]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt 0 x with
  | inl h => linarith [abs_of_nonneg h]
  | inr h => linarith [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x + y) with
  | inl h =>
    rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  | inr h =>
    rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  apply Iff.intro
  case mpr => -- showcase doing `mpr` first
    rintro (hp | hm)
    · linarith [le_abs_self y]
    · linarith [neg_le_abs_self y]
  case mp =>
    intro h
    cases le_or_gt 0 y with
    | inl h' =>
      left; rw [abs_of_nonneg h'] at h
      linarith [le_abs_self y]
    | inr h' =>
      right; rw [abs_of_neg h'] at h
      linarith [neg_le_abs_self y]

theorem lt_abs' : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h -- prefer `rcases` for destructuring disjunctions, as it provides syntactic checking
    cases' le_or_gt 0 y with h' h'  -- cases' with `with` gives cleaner syntax than structured cases
    · left; rwa [abs_of_nonneg h'] at h
    · right; rwa [abs_of_neg h'] at h  -- rwa = rewrite + assumption in one step
  · rintro (hp | hm) <;> linarith [le_abs_self y, neg_le_abs_self y]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor <;> intro h
  · rcases le_or_gt 0 y with yp|ym
    repeat · try constructor <;> linarith [neg_le_abs_self x, le_abs_self x]
  · have : y > 0 := by linarith [le_abs_self y, neg_le_abs_self y]
    rcases le_or_gt 0 x with xsgn|xsgn <;> [
      rw [abs_of_nonneg xsgn];
      rw [abs_of_neg xsgn]
    ] <;> linarith [this, h]


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, _ | _⟩ <;> linarith! [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this <;> [left; right] <;> linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this <;> [left; right] <;> linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by aesop
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases p:P <;> simp [*]
  · intro h p
    rcases h with (h | h)
    · contradiction
    · assumption
