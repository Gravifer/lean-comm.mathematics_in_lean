import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap End

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rcases h with ⟨P', Q', h⟩
  rw [Submodule.eq_bot_iff]
  rintro x hx; rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  obtain ⟨hxp, hxq⟩ := hx
  replace h := congr((aeval φ) $h.symm x)
  simp [hxp, hxq] at h; assumption

#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp
#check Polynomial
example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  ext x; simp [mem_ker, Submodule.mem_sup]; constructor <;> intro prec
  · rcases prec with ⟨y, hy, z, hz, rfl⟩
    have {φ : End K V} {P Q : K[X]}
          : (aeval φ) P * (aeval φ) Q = (aeval φ) Q * (aeval φ) P := by
      rw [← map_mul, ← map_mul, mul_comm]
    simp [hy, hz]; rw [← mul_apply, this, mul_apply, hy]; simp
  · rw [<-mul_apply, <-map_mul] at prec
    rcases h with ⟨P', Q', h⟩
    let y := aeval φ (Q'*Q) x
    let z := aeval φ (P'*P) x
    have key : y + z = x := by
      subst y z
      simpa [add_comm] using congr((aeval φ) $h x)
    use y, by
      subst y
      rw [<-mul_apply, <-map_mul, mul_comm Q', <-mul_assoc, mul_comm, map_mul, mul_apply, prec]
      simp
    use z, by
      subst z
      rw [<-mul_apply, <-map_mul, mul_comm, mul_assoc, map_mul, mul_apply, prec]
      simp


example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def



example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
