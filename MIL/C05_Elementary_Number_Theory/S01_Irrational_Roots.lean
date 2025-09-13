import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul -- that prime naturals are irreducible
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

lemma sqrt2_irrational {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  have lem {m n : ℕ} (se : m ^ 2 = 2 * n ^ 2) : 2 ∣ m := by apply even_of_even_sqr; try rw [se]; simp_all
  intro sqr_eq
  have : 2 ∣ m := lem sqr_eq
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by simp_all
  have : 2 ∣ n := lem this.symm
  have : 2 ∣ m.gcd n := by
    apply dvd_gcd
    repeat assumption
  have : 2 ∣ 1 := by
    rwa [coprime_mn] at this
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  have lem {m n p : ℕ} (prime_p : p.Prime) (se : m ^ 2 = p * n ^ 2) : p ∣ m := by
    apply Nat.Prime.dvd_of_dvd_pow prime_p; try rw [se]; simp_all
  have h : 2=p ∨ 2<p := by refine eq_or_lt_of_le ?_; exact prime_p.two_le
  rcases h with rfl | _
  · exact sqrt2_irrational coprime_mn
  · intro sqr_eq
    have : p ∣ m := lem prime_p sqr_eq
    obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
    have : p * (p * k ^ 2) = p * n ^ 2 := by
      rw [← sqr_eq, meq]
      ring
    have : p * k ^ 2 = n ^ 2 := by aesop
    have : p ∣ n := lem prime_p this.symm
    have : p ∣ m.gcd n := by
      apply dvd_gcd
      repeat assumption
    have : p ∣ 1 := by
      rwa [coprime_mn] at this
    exact Nat.Prime.not_dvd_one prime_p this

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

/- `n.factorization` is defined in Lean as a function of finite support,
    which explains the strange notation through the proofs -/
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    field_simp
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul', factorization_pow', Nat.Prime.factorization' prime_p]
    · exact Nat.add_comm 1 (2 * n.factorization p)
    repeat aesop
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [factorization_pow']
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul', factorization_pow']
    refine Nat.add_comm _ _
    · exact r.succ_ne_zero
    · exact npow_nz
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  rw [<-Nat.mul_sub k]
  apply dvd_def.mpr
  use (m.factorization p - n.factorization p)

#check multiplicity
