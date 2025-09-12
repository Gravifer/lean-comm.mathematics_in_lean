import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    · right
      use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor <;> intro h y ys <;> try simp
  · exact h ⟨y, ys, rfl⟩
  · rcases ys with ⟨x, xs, rfl⟩
    exact h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  field_simp

example : f '' (f ⁻¹' u) ⊆ u := by
  field_simp

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  field_simp

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  exact image_mono h

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  tauto -- classical used

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  field_simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  exact image_inter_subset f s t

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ⟨x', xt, hf⟩⟩
  have : x' = x := h hf
  rw [this] at xt
  have : x ∈ s ∩ t := ⟨xs, xt⟩
  use x, this

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨⟨x, xs, fx⟩, ynft⟩
  simp [*] at ynft
  have : x ∈ s \ t := mem_diff_of_mem xs fun a ↦ ynft x a fx
  use x
example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  field_simp

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  exact Eq.symm (image_inter_preimage f s v)

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  -- have h := image_inter_subset f s (f ⁻¹' u)
  intro y ⟨x, ⟨xs, xu⟩, fx⟩
  have : f x ∈ u := xu
  exact ⟨⟨x, xs, fx⟩, by rwa [<-fx]⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  exact inter_preimage_subset s u f

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  exact union_preimage_subset s u f

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  exact image_iUnion

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  exact image_iInter_subset A f

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy; simp_all; -- unfold Injective at *
  rcases hy i with ⟨x, xa, fxe⟩
  use x; constructor
  · intro j
    rcases hy j with ⟨x', x'a, fx'e⟩
    have : x' = x := injf (by rw [fxe, fx'e])
    bound
  · exact fxe

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  field_simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  exact preimage_iInter

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  -- unfold InjOn
  intro x xsgn y ysgn r; dsimp at *
  apply_fun (· ^ 2) at r
  rwa [sq_sqrt xsgn, sq_sqrt ysgn] at r

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xsgn y ysgn r; dsimp at *
  apply_fun sqrt at r
  rwa [sqrt_sq xsgn, sqrt_sq ysgn] at r

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor <;> simp_all
  · intros; bound
  · intros
    use y ^ 2
    field_simp

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor <;> simp_all
  · intros; bound
  · intros
    use sqrt y
    field_simp [sqrt_sq (by linarith)]

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  -- unfold Injective LeftInverse at *
  constructor <;> intro hf x
  · dsimp [inverse] at *
    have  : ∃ x1, f x1 = f x := ⟨x, rfl⟩
    simp [dif_pos h]; apply_fun f
    rw [choose_spec this]
  · intro x1 feq
    obtain hf0 := hf x
    obtain hf1 := hf x1
    rw [<-hf0, <-hf1]
    congr




example : Surjective f ↔ RightInverse (inverse f) f := by
  -- unfold Surjective RightInverse LeftInverse at *
  constructor <;> intro pr y
  · obtain ⟨x, fxeq⟩ := pr y
    exact inverse_spec y ⟨x, fxeq⟩
  · use inverse f y
    exact pr y


end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
