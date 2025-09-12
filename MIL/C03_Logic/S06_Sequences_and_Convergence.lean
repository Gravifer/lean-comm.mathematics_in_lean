import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h  -- when we apply an expr with an `_` and Lean can’t fill in automatically
  · rw [one_mul]  -- it simply leaves it for us as another goal
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  -- have ngeNs : n ≥ Ns := le_of_max_le_left hn
  -- have ngeNt : n ≥ Nt := le_of_max_le_right hn
  obtain hs := hs n $ le_of_max_le_left hn
  obtain ht := ht n $ by omega
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring
    _ ≤ |s n - a| + |t n - b| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add hs ht
    _ = ε := by ring

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  unfold ConvergesTo at cs
  intro ε εpos
  let ε₁ := ε / |c|;  have : 0 < ε₁ := div_pos εpos acpos
  rcases cs ε₁ this with ⟨N, h⟩; use N
  intro n nge; specialize h n nge
  calc  |c * s n - c * a|
    _ = |c * (s n - a)| := by group
    _ = |c| * |s n - a| := by rw [abs_mul]
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left h acpos
    _ = ε := by field_simp [acpos]

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn;  specialize h n hn
  calc
    |s n| = |s n - a + a| := by ring
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < |a| + 1 := by linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  specialize h₀ n (le_of_max_le_left  hn)
  specialize h₁ n (le_of_max_le_right hn); simp at h₁
  calc
    |s n * t n - 0| = |s n * t n| := by ring
    _ = |s n| * |t n| := by rw [abs_mul]
    _ < B * (ε / B) := by gcongr
    _ = ε := by field_simp [Bpos]

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs  -- `convert e` is similar to `refine e`, but the type of `e` is not required to exactly match the goal.
    convert convergesTo_add ct (convergesTo_const (-b))  -- Instead, new goals are created for differences
    ring  -- between the type of `e` and the goal using the same strategies as the `congr!` tactic.
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

example {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b)
    : a = b := by
  -- unfold ConvergesTo at *
  have: ∀ ε > 0, |a - b| < ε := by
    intro ε εpos
    rcases sa (ε / 2) (by linarith) with ⟨Na, hNa⟩
    rcases sb (ε / 2) (by linarith) with ⟨Nb, hNb⟩
    let N := max Na Nb
    have ngeNa : N ≥ Na := le_of_max_le_left (le_refl _)
    have ngeNb : N ≥ Nb := le_of_max_le_right (le_refl _)
    have absa : |s N - a| < ε / 2 := hNa N ngeNa
    have absb : |s N - b| < ε / 2 := hNb N ngeNb
    calc
      |a - b| = |a - s N + (s N - b)| := by ring
      _ ≤ |a - s N| + |s N - b| := abs_add _ _
      _ = |s N - a| + |s N - b| := by rw[abs_sub_comm]
      _ < ε / 2 + ε / 2 := by linarith -- add_lt_add absa absb
      _ = ε := by ring
  contrapose this; push_neg at *
  have: a - b ≠ 0 := by bound
  have: |a - b| > 0 := abs_pos.mpr this
  use |a - b|

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by refine hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := by refine hNb N (le_max_right _ _)
  have : |a - b| < |a - b| := by calc
    _ = |(-(s N - a)) + (s N - b)| := by  congr; ring
    _ ≤ |-(s N - a)| + |s N - b| := abs_add _ _
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := by linarith  -- add_lt_add absa abs
    _ = |a - b| := by norm_num [ε]
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
