import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx


noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro n m; rintro ⟨n, rfl⟩; rintro ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp


def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    suffices : φ 0 ∈ H; exact this
    rw [φ.map_zero]
    exact H.zero_mem'
  add_mem' := by
    rintro x1 x2 hx1 hx2
    simp_all
    exact H.add_mem hx1 hx2
  smul_mem' := by
    rintro a x hx
    simp_all
    exact H.smul_mem a hx

example (U : Submodule K V) : Module K U := inferInstance

example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

/-! #### Complete lattice structure and internal direct sums -/

example (H H' : Submodule K V) :
    ((H ⊓ H' : _) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

-- You can coerce the submodule to its underlying set
example : (⊤ : Submodule K V) = (Set.univ : Set V) := rfl
-- And there are ways to move elements back and forth
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial
-- There's typically a canonical isomorphism
noncomputable example : (⊤ : Submodule K V) ≃ₗ[K] V :=
  Submodule.topEquiv

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K


-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_iSupIndep.pairwiseDisjoint hij).eq_bot

-- Those conditions characterize direct sums.
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end

/-! #### Subspace spanned by a set -/

example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

/- `GaloisInsertion` is defined as a `struct` not a`class`,
    because there is no canonical one (because `choice` is arbitrarily valid) -/
example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
  | mem y h =>
      rcases h with h|h
      · use y, h, 0, T.zero_mem, by simp
      · use 0, S.zero_mem, y, h, by simp
  | zero => use 0, S.zero_mem, 0, T.zero_mem, by simp
  | add x y hx hy hx' hy' =>
      rcases hx' with ⟨sx, hsx, tx, htx, rfl⟩
      rcases hy' with ⟨sy, hsy, ty, hty, rfl⟩
      use sx + sy, S.add_mem hsx hsy, tx + ty, T.add_mem htx hty, by module
  | smul a x hx hx' =>
      rcases hx' with ⟨sx, hsx, tx, htx, rfl⟩
      use a • sx, S.smul_mem a hsx, a • tx, T.smul_mem a htx, by module

/-! #### Pushing and pulling subspaces -/
section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`



open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  constructor <;> intro prec
  · rintro x hx; simp
    suffices : φ x ∈ Submodule.map φ E; exact prec this
    use x, hx
  · rintro y ⟨x, hx, rfl⟩
    exact prec hx

/-! #### Quotient spaces -/

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange


open Submodule

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun := by
    intro F; let F' := comap E.mkQ F
    use F'; rw [← E.ker_mkQ, ← comap_bot]; subst F'
    gcongr; exact bot_le
  invFun := fun F => map E.mkQ F
  left_inv := by
    intro F; simp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq F
  right_inv := by
    intro ⟨F,hF⟩; ext
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact hF
