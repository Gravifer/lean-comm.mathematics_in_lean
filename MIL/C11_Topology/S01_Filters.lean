import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset := Subset.trans
  inter_sets := subset_inter

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by use 0; simp
    sets_of_superset := by
      rintro x y ⟨a, hx⟩ hxy
      use a; intro b hb
      exact hxy (hx b hb)
    inter_sets := by
      rintro x y ⟨a, hx⟩ ⟨a', hy⟩
      use max a a'; intro b hb
      refine ⟨hx b ?_, hy b ?_⟩
      all_goals simp_all
  }

variable (x ε : ℝ) in
#check Ioo (x - ε) (x + ε) -- interval open-open
variable (x ε : ℝ) in
#check Ioc (x - ε) (x + ε)

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F
/- The problem with `Tendsto₁` is that it exposes a quantifier and elements of `G`,
  and it hides the intuition that we get by viewing filters as generalized sets. -/
def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G -- `Filter.map` is the pushforward of `F` along `f`
#print Tendsto

lemma Tendsto₂iffTendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  -- rw [← Tendsto₂iffTendsto₁, Tendsto₂, ← map_map] at *
  calc map g (map f F)
    _ ≤ map g G := map_mono hf
    _ ≤ H := hg

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff

#print Filter.instSProd
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  rw [nhds_prod_eq]
  simp only [SProd.sprod]
  rw [tendsto_inf]
  unfold Tendsto
  simp only [← map_le_iff_le_comap, map_map]

/- The ordered type `Filter X` is actually a **complete** lattice,
    by using the trivial filter with `∅` in it as `⊥`.-/
set_option pp.proofs true in
example: ∀ α, 𝓟 ∅ = (⊥ : Filter α) := by -- simp -- the trivial filter
  intro α; unfold Filter.principal; congr
  show {t | ∅ ⊆ t} = @univ (Set α)
  simp

example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) (fun ε ↦ Ioo (x₀ - ε) (x₀ + ε)) :=
  nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

#check Filter.Eventually
/- the filter `μ.ae` of comeagre sets is not very useful as the source or target of `Tendsto`,
    but it can be conveniently used with `Eventually` to say that a property holds for almost every point. -/

#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  simp only [mem_closure_iff_clusterPt, ClusterPt]
  refine neBot_of_le (?_ : map u atTop ≤ (𝓝 x ⊓ 𝓟 M))
  have: map u atTop ≤ 𝓟 M := le_principal_iff.mpr huM
  exact le_inf hux this
