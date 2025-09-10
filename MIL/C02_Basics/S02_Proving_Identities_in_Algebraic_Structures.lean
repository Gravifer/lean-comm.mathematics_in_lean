import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [<-zero_add b, <-zero_add c, <-neg_add_cancel a]
  rw [add_assoc (-a) a, add_assoc (-a) a, h]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [<-zero_add a, <-zero_add c, <-neg_add_cancel b]
  rw [add_assoc (-b) b, add_assoc (-b) b, add_comm b, add_comm b, h]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, zero_add, zero_add]
  rw [add_right_cancel h]

variable (a b : R) in
#check @add_left_cancel (a:=a) (b:=b) (c:=-a)
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [<-add_neg_cancel_right 0 a, zero_add] at h
  apply add_left_cancel at h
  rw [h]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [<-neg_add_cancel_right 0 b, zero_add] at h
  apply add_right_cancel at h
  rw [h]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  nth_rewrite 2 [eq_neg_of_add_eq_zero (add_neg_cancel a)]
  rfl

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [<-one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  let b := a * a⁻¹;  have hb : b * b = b := by
    unfold b; rw [mul_assoc a, <-mul_assoc (a⁻¹), inv_mul_cancel, one_mul]
  have h : b = 1 := by
    nth_rw 1 [<-one_mul b, <-inv_mul_cancel b, mul_assoc, hb, inv_mul_cancel]
  exact h

theorem mul_one (a : G) : a * 1 = a := by
  rw [<-inv_mul_cancel a, <-mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h {a b₁ b₂ : G} : (b₁ * a = 1) ∧ (b₂ * a = 1) -> (b₁ = b₂) := by
    intro ⟨h1, h2⟩; rw [<-mul_one b₁, <-mul_one b₂, <-mul_inv_cancel a]
    rw [<-mul_assoc, <-mul_assoc, h1, h2]
  have h1 : (a * b)⁻¹ * (a * b) = 1 := inv_mul_cancel (a * b)
  have h2 : (b⁻¹ * a⁻¹) * (a * b) = 1 := by  group
  exact h ⟨h1, h2⟩

end MyGroup

end
