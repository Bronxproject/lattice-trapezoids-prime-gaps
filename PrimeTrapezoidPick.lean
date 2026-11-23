import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

namespace PrimeTrapezoidPick

/-- 0-indexed n-th prime: p 0 = 2, p 1 = 3, p 2 = 5, ... -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- n-th prime gap: g n = p (n + 1) - p n. -/
noncomputable def g (n : ℕ) : ℕ := p (n + 1) - p n

/-- Boundary lattice point count B_n of the prime trapezoid Q_n. -/
noncomputable def B (n : ℕ) : ℕ := 2 * g n + g (n + 1) + Nat.gcd (g n) (g (n + 1))

/-- Twice the interior lattice point count 2 * I_n (kept in ℤ for exact arithmetic). -/
noncomputable def twoI (n : ℕ) : ℤ :=
  (g n : ℤ) * ((g n : ℤ) + (g (n + 1) : ℤ))
    - 2 * (g n : ℤ) - (g (n + 1) : ℤ) - (Nat.gcd (g n) (g (n + 1)) : ℤ) + 2

/-! ### Basic prime and gap lemmas -/

lemma p_strictMono : StrictMono p :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma p_lt_succ (n : ℕ) : p n < p (n + 1) :=
  p_strictMono (Nat.lt_succ_self n)

lemma p_zero : p 0 = 2 := Nat.nth_prime_zero_eq_two
lemma p_one : p 1 = 3 := Nat.nth_prime_one_eq_three
lemma p_two : p 2 = 5 := Nat.nth_prime_two_eq_five

lemma p_of_count (m c : ℕ) (hm : Nat.Prime m) (hc : Nat.count Nat.Prime m = c) :
    p c = m := by
  have h := Nat.nth_count (p := Nat.Prime) hm
  rw [hc] at h
  exact h

lemma p_three : p 3 = 7 := p_of_count 7 3 (by norm_num) (by decide)
lemma p_four : p 4 = 11 := p_of_count 11 4 (by norm_num) (by decide)
lemma p_five : p 5 = 13 := p_of_count 13 5 (by norm_num) (by decide)

lemma p_prime (n : ℕ) : Nat.Prime (p n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

lemma g_pos (n : ℕ) : 0 < g n :=
  Nat.sub_pos_of_lt (p_lt_succ n)

lemma g_even {n : ℕ} (hn : 1 ≤ n) : Even (g n) := by
  have h1 : Odd (p n) := by
    rcases (p_prime n).eq_two_or_odd with h2 | hodd
    · exfalso
      have : p 0 < p n := p_strictMono (by omega)
      rw [p_zero, h2] at this
      omega
    · exact Nat.odd_iff.mpr hodd
  have h2 : Odd (p (n + 1)) := by
    rcases (p_prime (n + 1)).eq_two_or_odd with h2' | hodd
    · exfalso
      have : p 0 < p (n + 1) := p_strictMono (by omega)
      rw [p_zero, h2'] at this
      omega
    · exact Nat.odd_iff.mpr hodd
  exact Nat.Odd.sub_odd h2 h1

lemma g_ge_two {n : ℕ} (hn : 1 ≤ n) : 2 ≤ g n := by
  obtain ⟨k, hk⟩ := g_even hn
  have hpos := g_pos n
  omega

lemma even_ge_four_of_ge_two_ne_two {m : ℕ}
    (he : Even m) (hm : 2 ≤ m) (hne : m ≠ 2) : 4 ≤ m := by
  obtain ⟨t, ht⟩ := he
  omega

/-! ### Key factorization for 2 * I_n -/

lemma twoI_factor (n : ℕ) :
    twoI n = ((g n : ℤ) - 2) * ((g n : ℤ) + (g (n + 1) : ℤ))
      + 2 + ((g (n + 1) : ℤ) - (Nat.gcd (g n) (g (n + 1)) : ℤ)) := by
  unfold twoI
  ring

/-! ### Theorem A: Classification of minimal interior counts -/

/-- When g_n = 2 and n ≥ 1 (i.e., p_n is odd), 2 * I_n = g_{n+1}. -/
theorem twoI_of_g_eq_two {n : ℕ} (hn : 1 ≤ n) (hg : g n = 2) :
    twoI n = (g (n + 1) : ℤ) := by
  have hgcd : Nat.gcd (g n) (g (n + 1)) = 2 := by
    rw [hg]
    obtain ⟨k, hk⟩ := g_even (by omega : 1 ≤ n + 1)
    have hdiv : 2 ∣ g (n + 1) := ⟨k, by omega⟩
    exact Nat.gcd_eq_left hdiv
  rw [twoI_factor, hgcd, hg]
  ring

/-- For n ≥ 2 (so p_n ≥ 5), consecutive gaps cannot both be 2 (mod 3 obstruction). -/
lemma not_both_gaps_two {n : ℕ} (hn : 2 ≤ n) : ¬ (g n = 2 ∧ g (n + 1) = 2) := by
  rintro ⟨h1, h2⟩
  have hp_ge : 5 ≤ p n := by
    have := p_strictMono.monotone hn
    rwa [p_two] at this
  have hp1 : p (n + 1) = p n + 2 := by
    have := p_lt_succ n; unfold g at h1; omega
  have hp2 : p (n + 1 + 1) = p n + 4 := by
    have := p_lt_succ (n + 1); unfold g at h2; omega
  have hmod : p n % 3 = 0 ∨ p (n + 1) % 3 = 0 ∨ p (n + 1 + 1) % 3 = 0 := by omega
  rcases hmod with h0 | h0 | h0
  · have hdvd : 3 ∣ p n := Nat.dvd_of_mod_eq_zero h0
    rcases (p_prime n).eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
  · have hdvd : 3 ∣ p (n + 1) := Nat.dvd_of_mod_eq_zero h0
    rcases (p_prime (n + 1)).eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
  · have hdvd : 3 ∣ p (n + 1 + 1) := Nat.dvd_of_mod_eq_zero h0
    rcases (p_prime (n + 1 + 1)).eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega

/-- When g_n ≥ 4 and n ≥ 1, 2 * I_n ≥ 14 (i.e., I_n ≥ 7). -/
theorem twoI_ge_fourteen_of_g_ge_four {n : ℕ} (hn : 1 ≤ n) (hg : 4 ≤ g n) :
    14 ≤ twoI n := by
  have hg2 : 2 ≤ g (n + 1) := g_ge_two (by omega)
  have hgcd : Nat.gcd (g n) (g (n + 1)) ≤ g (n + 1) :=
    Nat.gcd_le_right (g n) (g_pos (n + 1))
  rw [twoI_factor]
  have h1 : (4 : ℤ) ≤ (g n : ℤ) := by exact_mod_cast hg
  have h2 : (2 : ℤ) ≤ (g (n + 1) : ℤ) := by exact_mod_cast hg2
  have h3 : (Nat.gcd (g n) (g (n + 1)) : ℤ) ≤ (g (n + 1) : ℤ) := by exact_mod_cast hgcd
  nlinarith

/-! ### Theorem B: Telescoping boundary sum -/

lemma sum_g (N : ℕ) : ∑ n ∈ range N, g n = p N - 2 := by
  induction N with
  | zero => simp [p_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hlt := p_lt_succ k
    have hge : 2 ≤ p k := by
      have := p_strictMono.monotone (Nat.zero_le k)
      rwa [p_zero] at this
    unfold g
    omega

lemma sum_g_succ (N : ℕ) : ∑ n ∈ range N, g (n + 1) = p (N + 1) - 3 := by
  induction N with
  | zero => simp [p_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hlt := p_lt_succ (k + 1)
    have hge : 3 ≤ p (k + 1) := by
      have := p_strictMono.monotone (by omega : 1 ≤ k + 1)
      rwa [p_one] at this
    unfold g
    omega

/-- Exact telescoping identity for the cumulative boundary count (1 ≤ N). -/
theorem sum_B_eq {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ range N, B n =
      3 * p N + g N - 7 + ∑ n ∈ range N, Nat.gcd (g n) (g (n + 1)) := by
  have hsplit : ∑ n ∈ range N, B n =
      2 * (∑ n ∈ range N, g n) + (∑ n ∈ range N, g (n + 1))
        + ∑ n ∈ range N, Nat.gcd (g n) (g (n + 1)) := by
    unfold B
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, sum_g, sum_g_succ]
  have hpN : 3 ≤ p N := by
    have := p_strictMono.monotone hN
    rwa [p_one] at this
  have hlt := p_lt_succ N
  unfold g
  omega

/-- Unconditional upper bound on the cumulative boundary count. -/
theorem sum_B_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ range N, B n ≤ 4 * p N + g N - 9 := by
  rw [sum_B_eq hN]
  have hgcd_sum : ∑ n ∈ range N, Nat.gcd (g n) (g (n + 1)) ≤ ∑ n ∈ range N, g n := by
    apply Finset.sum_le_sum
    intro n _
    exact Nat.gcd_le_left (g (n + 1)) (g_pos n)
  rw [sum_g] at hgcd_sum
  have hpN : 3 ≤ p N := by
    have := p_strictMono.monotone hN
    rwa [p_one] at this
  omega

/-! ### Concrete checks and edge cases -/

example : g 0 = 1 := by norm_num [g, p_zero, p_one]
example : g 1 = 2 := by norm_num [g, p_one, p_two]
example : g 2 = 2 := by norm_num [g, p_two, p_three]
example : g 3 = 4 := by norm_num [g, p_three, p_four]
example : g 4 = 2 := by norm_num [g, p_four, p_five]

example : twoI 0 = 0 := by
  norm_num [twoI, g, p_zero, p_one, p_two]
example : twoI 1 = 2 := by
  norm_num [twoI, g, p_one, p_two, p_three]
example : twoI 2 = 4 := by
  norm_num [twoI, g, p_two, p_three, p_four]
example : twoI 3 = 14 := by
  norm_num [twoI, g, p_three, p_four, p_five]

/-- The bound 14 is attained at n = 3, where the gaps are 4 and 2. -/
example : 14 ≤ twoI 3 :=
  twoI_ge_fourteen_of_g_ge_four (by omega) (by norm_num [g, p_three, p_four])

/-- The cutoff n ≥ 2 in `not_both_gaps_two` is sharp: the gaps after 3 are 2 and 2. -/
example : g 1 = 2 ∧ g 2 = 2 := by
  norm_num [g, p_one, p_two, p_three]

/-- The even-gap hypothesis starts at n = 1: the initial gap is odd. -/
example : ¬ Even (g 0) := by
  norm_num [g, p_zero, p_one]

/-- `sum_B_eq` also holds at N = 0, although its theorem currently assumes N ≥ 1. -/
example :
    (∑ n ∈ range 0, B n) =
      3 * p 0 + g 0 - 7 + ∑ n ∈ range 0, Nat.gcd (g n) (g (n + 1)) := by
  norm_num [B, g, p_zero, p_one]

/-- The upper bound is sharp at N = 1. -/
example : (∑ n ∈ range 1, B n) = 4 * p 1 + g 1 - 9 := by
  norm_num [B, g, p_zero, p_one, p_two]

/-- Every positive-index trapezoid has at least one interior point (2I ≥ 2). -/
theorem twoI_ge_two {n : ℕ} (hn : 1 ≤ n) : 2 ≤ twoI n := by
  by_cases hg : g n = 2
  · rw [twoI_of_g_eq_two hn hg]
    exact_mod_cast g_ge_two (by omega : 1 ≤ n + 1)
  · have hg4 : 4 ≤ g n := by
      obtain ⟨k, hk⟩ := g_even hn
      have hpos := g_pos n
      omega
    exact le_trans (by norm_num : (2 : ℤ) ≤ 14)
      (twoI_ge_fourteen_of_g_ge_four hn hg4)

/-- For n ≥ 2, the minimum interior count 2Iₙ = 4 occurs exactly at gaps (2, 4). -/
theorem twoI_eq_four_iff {n : ℕ} (hn : 2 ≤ n) :
    twoI n = 4 ↔ g n = 2 ∧ g (n + 1) = 4 := by
  constructor
  · intro h
    have hn1 : 1 ≤ n := by omega
    have hge2 : 2 ≤ g n := g_ge_two hn1
    have hlt4 : g n < 4 := by
      by_contra hnot
      have hge4 : 4 ≤ g n := by omega
      have h14 := twoI_ge_fourteen_of_g_ge_four hn1 hge4
      omega
    have heven := g_even hn1
    have hg2 : g n = 2 := by
      obtain ⟨t, ht⟩ := heven
      omega
    have htwoI := twoI_of_g_eq_two hn1 hg2
    refine ⟨hg2, ?_⟩
    omega
  · rintro ⟨hg2, hg4⟩
    rw [twoI_of_g_eq_two (by omega) hg2]
    exact_mod_cast hg4

/-- For n ≥ 1 and gₙ ≥ 4, equality 2Iₙ = 14 occurs exactly at gaps (4, 2). -/
theorem twoI_eq_fourteen_iff {n : ℕ} (hn : 1 ≤ n) (hg : 4 ≤ g n) :
    twoI n = 14 ↔ g n = 4 ∧ g (n + 1) = 2 := by
  have hy2 : 2 ≤ g (n + 1) := g_ge_two (by omega)
  have hgcd : Nat.gcd (g n) (g (n + 1)) ≤ g (n + 1) :=
    Nat.gcd_le_right (g n) (g_pos (n + 1))
  constructor
  · intro h
    have hfactor := twoI_factor n
    rw [hfactor] at h
    have hgZ : (4 : ℤ) ≤ (g n : ℤ) := by exact_mod_cast hg
    have hyZ : (2 : ℤ) ≤ (g (n + 1) : ℤ) := by exact_mod_cast hy2
    have hgcdZ : (Nat.gcd (g n) (g (n + 1)) : ℤ) ≤ (g (n + 1) : ℤ) :=
      by exact_mod_cast hgcd
    have hgn : g n = 4 := by
      by_contra hne
      have hg6 : 6 ≤ g n := by
        obtain ⟨t, ht⟩ := g_even hn
        omega
      have hg6Z : (6 : ℤ) ≤ (g n : ℤ) := by exact_mod_cast hg6
      have hprod :
          (32 : ℤ) ≤ ((g n : ℤ) - 2) * ((g n : ℤ) + (g (n + 1) : ℤ)) := by
        have hleft : 0 ≤ (g n : ℤ) - 6 := by omega
        have hright : 0 ≤ (g n : ℤ) + (g (n + 1) : ℤ) - 8 := by omega
        have hmul := mul_nonneg hleft hright
        nlinarith
      have hrest : (0 : ℤ) ≤ (g (n + 1) : ℤ) -
          (Nat.gcd (g n) (g (n + 1)) : ℤ) := by linarith
      linarith
    have hyn : g (n + 1) = 2 := by
      by_contra hne
      have hy4 : 4 ≤ g (n + 1) :=
        even_ge_four_of_ge_two_ne_two (g_even (by omega)) hy2 hne
      have hy4Z : (4 : ℤ) ≤ (g (n + 1) : ℤ) := by exact_mod_cast hy4
      have hprod : (16 : ℤ) ≤
          ((g n : ℤ) - 2) * ((g n : ℤ) + (g (n + 1) : ℤ)) := by
        rw [hgn]
        nlinarith
      have hrest : (0 : ℤ) ≤ (g (n + 1) : ℤ) -
          (Nat.gcd (g n) (g (n + 1)) : ℤ) := by linarith
      linarith
    exact ⟨hgn, hyn⟩
  · rintro ⟨hgn, hyn⟩
    rw [twoI_factor, hgn, hyn]
    norm_num

/-- Minimal-count theorem, base cases: I₁ = 0 (Lean n = 0) and I₂ = 1 (Lean n = 1). -/
theorem twoI_zero : twoI 0 = 0 := by
  norm_num [twoI, g, p_zero, p_one, p_two]

theorem twoI_one : twoI 1 = 2 := by
  norm_num [twoI, g, p_one, p_two, p_three]

/-- Minimal-count theorem, combined bound: for paper n ≥ 3 (Lean 2 ≤ n), 2 * Iₙ ≥ 4. -/
theorem twoI_ge_four {n : ℕ} (hn : 2 ≤ n) : 4 ≤ twoI n := by
  have hn1 : 1 ≤ n := by omega
  by_cases hg2 : g n = 2
  · have hnot := not_both_gaps_two hn
    have hnext2 : 2 ≤ g (n + 1) := g_ge_two (by omega)
    have hnext_ne : g (n + 1) ≠ 2 := by
      intro h
      exact hnot ⟨hg2, h⟩
    have hnext4 :=
      even_ge_four_of_ge_two_ne_two (g_even (by omega)) hnext2 hnext_ne
    rw [twoI_of_g_eq_two hn1 hg2]
    exact_mod_cast hnext4
  · have hg4 :=
      even_ge_four_of_ge_two_ne_two (g_even hn1) (g_ge_two hn1) hg2
    exact le_trans (by norm_num : (4 : ℤ) ≤ 14)
      (twoI_ge_fourteen_of_g_ge_four hn1 hg4)

end PrimeTrapezoidPick

#check PrimeTrapezoidPick.twoI_of_g_eq_two
#check PrimeTrapezoidPick.not_both_gaps_two
#check PrimeTrapezoidPick.twoI_ge_fourteen_of_g_ge_four
#check PrimeTrapezoidPick.twoI_ge_two
#check PrimeTrapezoidPick.twoI_eq_four_iff
#check PrimeTrapezoidPick.twoI_eq_fourteen_iff
#check PrimeTrapezoidPick.twoI_zero
#check PrimeTrapezoidPick.twoI_one
#check PrimeTrapezoidPick.twoI_ge_four
#check PrimeTrapezoidPick.sum_B_eq
#check PrimeTrapezoidPick.sum_B_le

#print axioms PrimeTrapezoidPick.twoI_of_g_eq_two
#print axioms PrimeTrapezoidPick.not_both_gaps_two
#print axioms PrimeTrapezoidPick.twoI_ge_fourteen_of_g_ge_four
#print axioms PrimeTrapezoidPick.twoI_ge_two
#print axioms PrimeTrapezoidPick.twoI_eq_four_iff
#print axioms PrimeTrapezoidPick.twoI_eq_fourteen_iff
#print axioms PrimeTrapezoidPick.twoI_zero
#print axioms PrimeTrapezoidPick.twoI_one
#print axioms PrimeTrapezoidPick.twoI_ge_four
#print axioms PrimeTrapezoidPick.sum_B_eq
#print axioms PrimeTrapezoidPick.sum_B_le

namespace PrimeTrapezoidPick

/-! ### Geometric bridge: actual interior lattice points of the shifted trapezoid -/

/-- Strict interior lattice points of the shifted trapezoid Q_n with gaps a = g_n, b = g_{n+1}. -/
def interiorPoints (a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range a).product (Finset.range (a + b))).filter
    (fun uv => 0 < uv.1 ∧ uv.1 < uv.2 ∧ a * uv.2 < a * a + b * uv.1)

/-- Number of valid vertical lattice points v for a fixed x-slice u ∈ {1, ..., a-1}. -/
lemma card_slice {a b u : ℕ} (ha : 0 < a) (hb : 0 < b) (hu0 : 0 < u) (hua : u < a) :
    ((Finset.range (a + b)).filter (fun v => u < v ∧ a * v < a * a + b * u)).card
      = (a - u) + (b * u - 1) / a := by
  have hbu : 0 < b * u := Nat.mul_pos hb hu0
  have hsplit : (a * a + b * u - 1) / a = a + (b * u - 1) / a := by
    have hrewrite : a * a + b * u - 1 = (b * u - 1) + a * a := by omega
    rw [hrewrite, Nat.add_mul_div_left _ _ ha, add_comm]
  have hdiv_lt : (b * u - 1) / a < b := by
    apply (Nat.div_lt_iff_lt_mul ha).2
    have hprod : b * u < b * a := Nat.mul_lt_mul_of_pos_left hua hb
    omega
  have hset : (Finset.range (a + b)).filter (fun v => u < v ∧ a * v < a * a + b * u)
      = Finset.Ico (u + 1) (a + (b * u - 1) / a + 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, huv, hlt⟩
      refine ⟨by omega, ?_⟩
      have hle : a * v ≤ a * a + b * u - 1 := by omega
      have hdiv : v ≤ (a * a + b * u - 1) / a :=
        (Nat.le_div_iff_mul_le ha).mpr (by rw [mul_comm]; exact hle)
      rw [hsplit] at hdiv
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, by omega, ?_⟩
      have hv : v ≤ a + (b * u - 1) / a := by omega
      have hmul : a * ((b * u - 1) / a) ≤ b * u - 1 := Nat.mul_div_le (b * u - 1) a
      have hv_mul : a * v ≤ a * a + a * ((b * u - 1) / a) := by
        calc
          a * v ≤ a * (a + (b * u - 1) / a) := Nat.mul_le_mul_left a hv
          _ = a * a + a * ((b * u - 1) / a) := by rw [Nat.mul_add]
      have hbound : a * v ≤ a * a + b * u - 1 := by
        calc
          a * v ≤ a * a + a * ((b * u - 1) / a) := hv_mul
          _ ≤ a * a + (b * u - 1) := Nat.add_le_add_left hmul _
          _ ≤ a * a + b * u - 1 := by omega
      have hsum_pos : 0 < a * a + b * u := by omega
      have hstrict : a * a + b * u - 1 < a * a + b * u := by omega
      exact lt_of_le_of_lt hbound hstrict
  rw [hset, Nat.card_Ico]
  have hau : a - u + u = a := Nat.sub_add_cancel (le_of_lt hua)
  have hsum : a + (b * u - 1) / a + 1
      = (a - u + (b * u - 1) / a) + (u + 1) := by omega
  have hle : u + 1 ≤ a + (b * u - 1) / a + 1 := by
    calc
      u + 1 ≤ a + 1 := Nat.succ_le_succ (le_of_lt hua)
      _ ≤ a + 1 + (b * u - 1) / a :=
        Nat.add_le_add_left (Nat.zero_le _) (a + 1)
      _ = a + (b * u - 1) / a + 1 := by omega
  apply (Nat.sub_eq_iff_eq_add hle).2
  exact hsum

/-- Gauss pairing for a single term u and a - u. -/
lemma floor_pair {a b u : ℕ} (ha : 0 < a) (hb : 0 < b) (hu0 : 0 < u) (hua : u < a) :
    (b * u - 1) / a + (b * (a - u) - 1) / a =
      if a ∣ b * u then b - 2 else b - 1 := by
  have hbu : 0 < b * u := Nat.mul_pos hb hu0
  have hbau : 0 < b * (a - u) := Nat.mul_pos hb (by omega)
  have hsum : b * u + b * (a - u) = b * a := by
    rw [← Nat.mul_add, Nat.add_sub_of_le (le_of_lt hua)]
  split_ifs with hdvd
  · obtain ⟨k, hk⟩ := hdvd
    have hk_pos : 0 < k := by nlinarith
    have hk_lt : k < b := by nlinarith
    have h1 : (b * u - 1) / a = k - 1 := by
      rw [hk]
      have : a * k - 1 = (a - 1) + a * (k - 1) := by
        have hk_decomp : k = (k - 1) + 1 := by omega
        have hmul : a * k = a * (k - 1) + a := by
          calc
            a * k = a * ((k - 1) + 1) := congrArg (fun t => a * t) hk_decomp
            _ = a * (k - 1) + a := by simp [Nat.mul_add]
        rw [hmul]
        omega
      rw [this, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (by omega : a - 1 < a), zero_add]
    have h2 : (b * (a - u) - 1) / a = b - k - 1 := by
      have hbau_eq : b * (a - u) = a * (b - k) := by
        have hsum' : a * k + b * (a - u) = a * b := by
          calc
            a * k + b * (a - u) = b * u + b * (a - u) := by rw [hk]
            _ = b * a := hsum
            _ = a * b := Nat.mul_comm b a
        have hk_decomp : b - k + k = b := by omega
        have hprod : a * (b - k) + a * k = a * b := by
          calc
            a * (b - k) + a * k = a * ((b - k) + k) := by rw [Nat.mul_add]
            _ = a * b := by rw [hk_decomp]
        have hprod' : a * k + a * (b - k) = a * b := by
          simpa [Nat.add_comm] using hprod
        exact Nat.add_left_cancel (hsum'.trans hprod'.symm)
      rw [hbau_eq]
      have hbk_pos : 0 < b - k := by omega
      have : a * (b - k) - 1 = (a - 1) + a * (b - k - 1) := by
        have hbk_decomp : b - k = (b - k - 1) + 1 := by omega
        have hmul : a * (b - k) = a * (b - k - 1) + a := by
          calc
            a * (b - k) = a * ((b - k - 1) + 1) := congrArg (fun t => a * t) hbk_decomp
            _ = a * (b - k - 1) + a := by simp [Nat.mul_add]
        rw [hmul]
        omega
      rw [this, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (by omega : a - 1 < a), zero_add]
    omega
  · set q := (b * u) / a
    set r := (b * u) % a
    have hr_pos : 0 < r := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
    have hr_lt : r < a := Nat.mod_lt _ ha
    have hdiv_eq : a * q + r = b * u := Nat.div_add_mod (b * u) a
    have h1 : (b * u - 1) / a = q := by
      have : b * u - 1 = (r - 1) + a * q := by omega
      rw [this, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (by omega : r - 1 < a), zero_add]
    have hq_lt : q < b := by nlinarith
    have h2 : (b * (a - u) - 1) / a = b - q - 1 := by
      have : b * (a - u) - 1 = (a - r - 1) + a * (b - q - 1) := by
        have hba : b * a = a * b := mul_comm b a
        have : a * (b - q - 1) + a * q + a = a * b := by
          have : (b - q - 1) + q + 1 = b := by omega
          nlinarith
        omega
      rw [this, Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (by omega : a - r - 1 < a), zero_add]
    omega

/-! ### Closing the geometric bridge: 2 * |interiorPoints| = twoI n -/

/-- Express the cardinality of `interiorPoints a b` as a sum over vertical slices
u ∈ [1, a). -/
lemma card_interiorPoints_eq_sum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (interiorPoints a b).card =
      ∑ u ∈ Finset.Ico 1 a, (a - u + (b * u - 1) / a) := by
  unfold interiorPoints
  rw [Finset.card_filter]
  change (∑ uv ∈ Finset.range a ×ˢ Finset.range (a + b),
    if 0 < uv.1 ∧ uv.1 < uv.2 ∧ a * uv.2 < a * a + b * uv.1 then 1 else 0) = _
  rw [Finset.sum_product]
  have hrange : Finset.range a = insert 0 (Finset.Ico 1 a) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  have hzero : (∑ v ∈ Finset.range (a + b),
      if 0 < (0 : ℕ) ∧ 0 < v ∧ a * v < a * a + b * 0 then 1 else 0) = 0 := by
    simp
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_Ico] at hu
  have hu0 : 0 < u := by omega
  have hslice := card_slice ha hb hu.1 hu.2
  rw [Finset.card_filter] at hslice
  simpa [hu0] using hslice

/-- Count of u ∈ [1, a) such that a ∣ b * u is gcd(a, b) - 1. -/
lemma card_filter_dvd {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    ((Finset.Ico 1 a).filter (fun u => a ∣ b * u)).card = Nat.gcd a b - 1 := by
  set d := Nat.gcd a b
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left b ha
  set a' := a / d
  set b' := b / d
  have ha_eq : a' * d = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hb_eq : b' * d = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have ha'_pos : 0 < a' := by nlinarith
  have hcop : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hd_pos
  have hdvd_iff : ∀ u, a ∣ b * u ↔ a' ∣ u := by
    intro u
    constructor
    · intro h
      have hda : d * a' = a := by rw [mul_comm, ha_eq]
      have hdbu : d * (b' * u) = b * u := by rw [← hb_eq]; ring
      have h1 : d * a' ∣ d * (b' * u) := by
        rw [hda, hdbu]
        exact h
      have h2 : a' ∣ b' * u := (Nat.mul_dvd_mul_iff_left hd_pos).mp h1
      exact hcop.dvd_of_dvd_mul_left h2
    · rintro ⟨k, rfl⟩
      refine ⟨b' * k, ?_⟩
      calc b * (a' * k) = (b' * d) * (a' * k) := by rw [hb_eq]
        _ = (a' * d) * (b' * k) := by ring
        _ = a * (b' * k) := by rw [ha_eq]
  have hcard : ((Finset.Ico 1 a).filter (fun u => a ∣ b * u)).card =
      (Finset.Ico 1 d).card := by
    symm
    apply Finset.card_bij (fun k _ => k * a')
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_filter, Finset.mem_Ico, hdvd_iff]
      refine ⟨⟨by nlinarith, ?_⟩, ⟨k, mul_comm k a'⟩⟩
      calc k * a' < d * a' := Nat.mul_lt_mul_of_pos_right hk.2 ha'_pos
        _ = a := by rw [mul_comm, ha_eq]
    · intro k1 _ k2 _ h
      exact Nat.eq_of_mul_eq_mul_right ha'_pos h
    · intro u hu
      rw [Finset.mem_filter, Finset.mem_Ico, hdvd_iff] at hu
      obtain ⟨k, hk⟩ := hu.2
      refine ⟨k, ?_, by rw [hk, mul_comm]⟩
      rw [Finset.mem_Ico]
      constructor
      · by_contra h0
        push Not at h0
        have : k = 0 := by omega
        rw [this, mul_zero] at hk
        omega
      · by_contra hge
        push Not at hge
        have : a ≤ u := by
          calc a = a' * d := ha_eq.symm
            _ ≤ a' * k := Nat.mul_le_mul_left a' hge
            _ = u := hk.symm
        omega
  rw [hcard, Nat.card_Ico]

/-- Pairing identity: 2 * ∑_{u=1}^{a-1} (a - u) = (a - 1) * a. -/
lemma two_mul_sum_sub (a : ℕ) :
    2 * ∑ u ∈ Finset.Ico 1 a, (a - u) = (a - 1) * a := by
  have hrev : ∑ u ∈ Finset.Ico 1 a, (a - u) =
      ∑ u ∈ Finset.Ico 1 a, u := by
    apply Finset.sum_bij (fun u _ => a - u)
    · intro u hu
      rw [Finset.mem_Ico] at hu ⊢
      omega
    · intro u1 hu1 u2 hu2 h
      rw [Finset.mem_Ico] at hu1 hu2
      omega
    · intro v hv
      rw [Finset.mem_Ico] at hv
      exact ⟨a - v, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro u hu
      rfl
  have h2 : 2 * ∑ u ∈ Finset.Ico 1 a, (a - u) =
      ∑ u ∈ Finset.Ico 1 a, ((a - u) + u) := by
    rw [two_mul, Finset.sum_add_distrib]
    nth_rw 2 [hrev]
  rw [h2]
  have hconst : ∑ u ∈ Finset.Ico 1 a, ((a - u) + u) =
      ∑ _u ∈ Finset.Ico 1 a, a := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_Ico] at hu
    omega
  rw [hconst, Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- Pairing identity for the floor sum in ℤ. -/
lemma two_mul_sum_floor {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    2 * (∑ u ∈ Finset.Ico 1 a, ((b * u - 1) / a : ℕ) : ℤ) =
      ((a : ℤ) - 1) * ((b : ℤ) - 1) - ((Nat.gcd a b : ℤ) - 1) := by
  have hrev : (∑ u ∈ Finset.Ico 1 a, ((b * u - 1) / a : ℕ)) =
      ∑ u ∈ Finset.Ico 1 a, ((b * (a - u) - 1) / a : ℕ) := by
    apply Finset.sum_bij (fun u _ => a - u)
    · intro u hu
      rw [Finset.mem_Ico] at hu ⊢
      omega
    · intro u1 hu1 u2 hu2 h
      rw [Finset.mem_Ico] at hu1 hu2
      omega
    · intro v hv
      rw [Finset.mem_Ico] at hv
      exact ⟨a - v, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro u hu
      congr 1
      rw [Finset.mem_Ico] at hu
      have hsub : a - (a - u) = u := by omega
      rw [hsub]
  have h2 : 2 * (∑ u ∈ Finset.Ico 1 a, ((b * u - 1) / a : ℕ)) =
      ∑ u ∈ Finset.Ico 1 a,
        ((b * u - 1) / a + (b * (a - u) - 1) / a) := by
    rw [two_mul, Finset.sum_add_distrib]
    nth_rw 2 [hrev]
  have hcast : 2 * (∑ u ∈ Finset.Ico 1 a, ((b * u - 1) / a : ℕ) : ℤ) =
      ∑ u ∈ Finset.Ico 1 a,
        (((b * u - 1) / a + (b * (a - u) - 1) / a : ℕ) : ℤ) := by
    norm_cast
  rw [hcast]
  have hterm :
      ∑ u ∈ Finset.Ico 1 a,
        (((b * u - 1) / a + (b * (a - u) - 1) / a : ℕ) : ℤ) =
      ∑ u ∈ Finset.Ico 1 a,
        (((b : ℤ) - 1) - if a ∣ b * u then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [floor_pair ha hb hu.1 hu.2]
    split_ifs with hdvd
    · have hb2 : 2 ≤ b := by
        by_contra hlt
        push Not at hlt
        have hb1 : b = 1 := by omega
        rw [hb1, one_mul] at hdvd
        have hle := Nat.le_of_dvd hu.1 hdvd
        omega
      omega
    · omega
  rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hfilt : (∑ u ∈ Finset.Ico 1 a, (if a ∣ b * u then (1 : ℤ) else 0)) =
      ((Nat.gcd a b : ℤ) - 1) := by
    have h1 : (∑ u ∈ Finset.Ico 1 a, (if a ∣ b * u then (1 : ℤ) else 0)) =
        (((Finset.Ico 1 a).filter (fun u => a ∣ b * u)).card : ℤ) := by
      simp [Finset.sum_boole]
    rw [h1, card_filter_dvd ha hb]
    have hd : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    omega
  rw [hfilt]
  have ha1 : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
  rw [ha1]

/-- Main geometric bridge: 2 * |interiorPoints (g n) (g (n + 1))| = twoI n for all n. -/
theorem two_mul_card_interiorPoints (n : ℕ) :
    2 * ((interiorPoints (g n) (g (n + 1))).card : ℤ) = twoI n := by
  have ha : 0 < g n := g_pos n
  have hb : 0 < g (n + 1) := g_pos (n + 1)
  rw [card_interiorPoints_eq_sum ha hb]
  simp only [Nat.cast_sum, Nat.cast_add]
  rw [Finset.sum_add_distrib]
  rw [mul_add]
  have hsub : 2 * (∑ u ∈ Finset.Ico 1 (g n), ((g n - u : ℕ) : ℤ)) =
      ((g n : ℤ) - 1) * (g n : ℤ) := by
    have h := two_mul_sum_sub (g n)
    have hcast : (2 * ∑ u ∈ Finset.Ico 1 (g n), (g n - u) : ℤ) =
        (((g n - 1) * g n : ℕ) : ℤ) := by
      exact_mod_cast h
    have ha1 : ((g n - 1 : ℕ) : ℤ) = (g n : ℤ) - 1 := by omega
    push_cast at hcast
    rw [ha1] at hcast
    exact hcast
  rw [hsub, two_mul_sum_floor ha hb]
  unfold twoI
  ring

example : (interiorPoints 2 2).card = 1 := by decide
example : (interiorPoints 2 4).card = 2 := by decide
example : (interiorPoints 4 2).card = 7 := by decide

example : twoI 2 = 4 ↔ g 2 = 2 ∧ g 3 = 4 :=
  twoI_eq_four_iff (by omega)

example : twoI 3 = 14 ↔ g 3 = 4 ∧ g 4 = 2 :=
  twoI_eq_fourteen_iff (by omega) (by norm_num [g, p_three, p_four])

end PrimeTrapezoidPick

#check PrimeTrapezoidPick.interiorPoints
#check PrimeTrapezoidPick.card_slice
#check PrimeTrapezoidPick.floor_pair
#check PrimeTrapezoidPick.two_mul_card_interiorPoints

#print axioms PrimeTrapezoidPick.card_slice
#print axioms PrimeTrapezoidPick.floor_pair
#print axioms PrimeTrapezoidPick.two_mul_card_interiorPoints

#eval (PrimeTrapezoidPick.interiorPoints 2 2).card
#eval (PrimeTrapezoidPick.interiorPoints 2 4).card
