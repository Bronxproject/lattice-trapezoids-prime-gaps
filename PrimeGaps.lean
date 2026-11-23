import Mathlib

open Finset

namespace PrimeGaps

/-! Lean indexes from 0, so `p 0 = 2`, `p 1 = 3`. The paper's p_n is `p (n-1)`. -/

noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Natural-valued prime gap, matching `PrimeTrapezoidPick.g`. -/
noncomputable def g (n : ℕ) : ℕ := p (n + 1) - p n

theorem p0 : p 0 = 2 := Nat.nth_prime_zero_eq_two

theorem p1 : p 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rw [hc] at h
  exact h

theorem p2 : p 2 = 5 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  rw [hc] at h
  exact h

theorem p_strictMono : StrictMono p :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem p_lt (n : ℕ) : p n < p (n + 1) := p_strictMono (Nat.lt_succ_self n)

theorem p_odd (n : ℕ) (hn : 1 ≤ n) : Odd (p n) := by
  have h0 : p 0 < p n := p_strictMono (by omega)
  have h2 : p 0 = 2 := Nat.nth_prime_zero_eq_two
  rcases (Nat.prime_nth_prime n).eq_two_or_odd' with h | h
  · exfalso
    have : p n = 2 := h
    omega
  · exact h

/-- Even gaps for n ≥ 1 (paper's "n ≥ 2"). -/
theorem gap_even (n : ℕ) (hn : 1 ≤ n) : Even (p (n + 1) - p n) := by
  obtain ⟨a, ha⟩ := p_odd (n + 1) (by omega)
  obtain ⟨b, hb⟩ := p_odd n hn
  exact ⟨a - b, by omega⟩

/-! Areas, computed over ℚ so that no truncated subtraction is involved. -/

noncomputable def gq (n : ℕ) : ℚ := (p (n + 1) : ℚ) - p n

/-- Area of the trapezoid above the horizontal axis. -/
noncomputable def A (n : ℕ) : ℚ :=
  ((p (n + 1) : ℚ) + p (n + 1 + 1)) * ((p (n + 1) : ℚ) - p n) / 2

/-- Area of the trapezoid below y = x. -/
noncomputable def E (n : ℕ) : ℚ :=
  ((p (n + 1) : ℚ) + p n) * ((p (n + 1) : ℚ) - p n) / 2

theorem gq_eq (n : ℕ) : gq n = ((p (n + 1) - p n : ℕ) : ℚ) := by
  unfold gq
  rw [Nat.cast_sub (p_lt n).le]

theorem gq_pos (n : ℕ) : 0 < gq n := by
  unfold gq
  have h : (p n : ℚ) < p (n + 1) := by exact_mod_cast p_lt n
  linarith

/-- Lemma 1: ΔA_n = ½ g_n (g_n + g_{n+1}). -/
theorem lemma1 (n : ℕ) : A n - E n = gq n * (gq n + gq (n + 1)) / 2 := by
  unfold A E gq
  ring

/-- Hand check: primes 2, 3, 5 give gaps 1 and 2, so ΔA = ½·1·(1+2) = 3/2. -/
example : A 0 - E 0 = 3 / 2 := by
  rw [lemma1]
  norm_num [gq, p0, p1, p2]

/-- ΔA_n > 0 for every prime-gap pair. -/
theorem delta_pos (n : ℕ) : 0 < A n - E n := by
  rw [lemma1]
  have h1 := gq_pos n
  have h2 := gq_pos (n + 1)
  positivity

/-- For n ≥ 1, g_n = 2a, g_{n+1} = 2b and ΔA_n = 2a(a+b). -/
theorem delta_even (n : ℕ) (hn : 1 ≤ n) :
    ∃ a b : ℕ, gq n = 2 * a ∧ gq (n + 1) = 2 * b ∧ A n - E n = 2 * a * (a + b) := by
  obtain ⟨a, ha⟩ := gap_even n hn
  obtain ⟨b, hb⟩ := gap_even (n + 1) (by omega)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [gq_eq, ha]; push_cast; ring
  · rw [gq_eq, hb]; push_cast; ring
  · rw [lemma1, gq_eq, gq_eq, ha, hb]; push_cast; ring

/-- Eq. (8): the cumulative deviation splits into the two sums. -/
theorem sum_delta_eq (N : ℕ) :
    ∑ n ∈ range N, (A n - E n)
      = (∑ n ∈ range N, gq n ^ 2) / 2 + (∑ n ∈ range N, gq n * gq (n + 1)) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lemma1]
  ring

/-- Finite upper bound with an endpoint term g_N²/4.
This implies the manuscript's bound by ∑_{n≤N} g_n². -/
theorem theorem2_corrected (N : ℕ) :
    ∑ n ∈ range N, (A n - E n) ≤ ∑ n ∈ range N, gq n ^ 2 + gq N ^ 2 / 4 := by
  have hshift : ∑ n ∈ range N, gq (n + 1) ^ 2 + gq 0 ^ 2
      = ∑ n ∈ range N, gq n ^ 2 + gq N ^ 2 := by
    have h1 := Finset.sum_range_succ' (fun n => gq n ^ 2) N
    have h2 := Finset.sum_range_succ (fun n => gq n ^ 2) N
    linarith
  have hcs : 2 * ∑ n ∈ range N, gq n * gq (n + 1)
      ≤ ∑ n ∈ range N, gq n ^ 2 + ∑ n ∈ range N, gq (n + 1) ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => by nlinarith [sq_nonneg (gq n - gq (n + 1))]
  rw [sum_delta_eq]
  have h0 : 0 ≤ gq 0 ^ 2 := sq_nonneg _
  linarith

/-! The formalization here concerns exact finite identities and inequalities.
The manuscript's asymptotic estimates and empirical statistics are not proved by this module. -/

#print axioms PrimeGaps.lemma1
#print axioms PrimeGaps.delta_pos
#print axioms PrimeGaps.delta_even
#print axioms PrimeGaps.sum_delta_eq
#print axioms PrimeGaps.theorem2_corrected

end PrimeGaps
