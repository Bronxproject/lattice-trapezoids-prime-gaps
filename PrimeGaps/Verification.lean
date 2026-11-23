import Mathlib
import PrimeGaps

/-! Verification checks and examples for the PrimeGaps formalization. -/

open Finset

namespace PrimeGaps

/-! ## A. Concrete values: do the definitions match real primes? -/

theorem p_of_count (m c : ℕ) (hm : m.Prime) (hc : Nat.count Nat.Prime m = c) : p c = m := by
  have h := Nat.nth_count (p := Nat.Prime) hm
  rw [hc] at h
  exact h

theorem v0 : p 0 = 2 := Nat.nth_prime_zero_eq_two
theorem v1 : p 1 = 3 := p_of_count 3 1 (by norm_num) (by decide)
theorem v2 : p 2 = 5 := p_of_count 5 2 (by norm_num) (by decide)
theorem v3 : p 3 = 7 := p_of_count 7 3 (by norm_num) (by decide)
theorem v4 : p 4 = 11 := p_of_count 11 4 (by norm_num) (by decide)

-- Gaps (1,2): ΔA = ½·1·(1+2) = 3/2
theorem dA0 : A 0 - E 0 = 3 / 2 := by
  rw [lemma1]; norm_num [gq, v0, v1, v2]

-- Gaps (2,2): ΔA = ½·2·(2+2) = 4
theorem dA1 : A 1 - E 1 = 4 := by
  rw [lemma1]; norm_num [gq, v1, v2, v3]

-- Gaps (2,4): ΔA = ½·2·(2+4) = 6
theorem dA2 : A 2 - E 2 = 6 := by
  rw [lemma1]; norm_num [gq, v2, v3, v4]

/-! ## B. Which hypotheses are necessary? -/

/-- `1 ≤ n` is NECESSARY in `p_odd`: the prime p 0 = 2 is even. -/
example : ¬ Odd (p 0) := by
  rw [v0, Nat.odd_iff]; norm_num

/-- ... and in `delta_even`: at n = 0 the gap g₀ = 1 is not of the form 2a. -/
theorem gap_zero_not_even : ¬ ∃ a : ℕ, gq 0 = 2 * a := by
  rintro ⟨a, ha⟩
  have h1 : gq 0 = 1 := by norm_num [gq, v0, v1]
  rw [h1] at ha
  have h2 : (1 : ℕ) = 2 * a := by exact_mod_cast ha
  omega

/-- ... so ΔA₀ = 3/2 is not even an integer: the evenness claim really needs n ≥ 1. -/
example : ¬ ∃ m : ℤ, A 0 - E 0 = m := by
  rintro ⟨m, hm⟩
  rw [dA0] at hm
  have h : (3 : ℚ) = 2 * m := by linarith
  have h' : (3 : ℤ) = 2 * m := by exact_mod_cast h
  omega

/-- Working in ℕ would silently change the meaning (truncated subtraction). -/
example : (p 0 - p 1 : ℕ) = 0 := by
  rw [v0, v1]
example : (p 0 : ℚ) - p 1 = -1 := by
  rw [v0, v1]; norm_num

/-! ## C. Stronger / weaker variants: where is the claim tight, where does it break? -/

/-- STRONGER than `delta_pos`: for n ≥ 1, ΔAₙ ≥ 4. -/
theorem delta_ge_four (n : ℕ) (hn : 1 ≤ n) : 4 ≤ A n - E n := by
  obtain ⟨a, b, ha, hb, h⟩ := delta_even n hn
  have ha0 : (0 : ℚ) < 2 * a := by
    have := gq_pos n; rw [ha] at this; exact this
  have hb0 : (0 : ℚ) < 2 * b := by
    have := gq_pos (n + 1); rw [hb] at this; exact this
  have ha' : 0 < a := by
    have : (0 : ℚ) < a := by linarith
    exact_mod_cast this
  have hb' : 0 < b := by
    have : (0 : ℚ) < b := by linarith
    exact_mod_cast this
  have ha1 : (1 : ℚ) ≤ a := by
    have : 1 ≤ a := by omega
    exact_mod_cast this
  have hb1 : (1 : ℚ) ≤ b := by
    have : 1 ≤ b := by omega
    exact_mod_cast this
  rw [h]
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1),
             mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 ha1)]

/-- The bound 4 is SHARP: equality at n = 1 (dA1 above). -/
example : A 1 - E 1 = 4 := dA1

/-- TOO STRONG: "ΔAₙ is a multiple of 4" is false (ΔA₂ = 6). -/
example : ¬ ∃ m : ℤ, A 2 - E 2 = 4 * m := by
  rintro ⟨m, hm⟩
  rw [dA2] at hm
  have h : (6 : ℤ) = 4 * m := by exact_mod_cast hm
  omega

/-- A tempting *stronger* inequality is false at N = 1:
ΔA₀ = 3/2 > 1 = g₀². The manuscript uses an upper bound that includes an
additional squared gap, and `theorem2_corrected` supplies the endpoint term. -/
theorem naive_upper_bound_false_at_N1 :
    ¬ (∑ n ∈ range 1, (A n - E n) ≤ ∑ n ∈ range 1, gq n ^ 2) := by
  rw [Finset.sum_range_one, Finset.sum_range_one, lemma1]
  norm_num [gq, v0, v1, v2]

/-- The corrected version holds at the same N (sanity: it is not violated). -/
example : ∑ n ∈ range 1, (A n - E n) ≤ ∑ n ∈ range 1, gq n ^ 2 + gq 1 ^ 2 / 4 :=
  theorem2_corrected 1

/-! ## D. What do the proofs actually use? Almost nothing about primes. -/

noncomputable def Agen (q : ℕ → ℚ) (n : ℕ) : ℚ :=
  (q (n + 1) + q (n + 1 + 1)) * (q (n + 1) - q n) / 2

noncomputable def Egen (q : ℕ → ℚ) (n : ℕ) : ℚ :=
  (q (n + 1) + q n) * (q (n + 1) - q n) / 2

/-- Our A is the general construction applied to the primes. -/
theorem A_eq_Agen (n : ℕ) : A n = Agen (fun k => (p k : ℚ)) n := rfl

/-- Lemma 1 is pure algebra: true for ANY sequence. -/
theorem lemma1_general (q : ℕ → ℚ) (n : ℕ) :
    Agen q n - Egen q n = (q (n + 1) - q n) * (q (n + 1 + 1) - q n) / 2 := by
  unfold Agen Egen; ring

/-- Positivity needs only strict monotonicity, not primality. -/
theorem delta_pos_general (q : ℕ → ℚ) (hq : StrictMono q) (n : ℕ) :
    0 < Agen q n - Egen q n := by
  rw [lemma1_general]
  have h1 : 0 < q (n + 1) - q n := sub_pos.2 (hq (Nat.lt_succ_self n))
  have h2 : 0 < q (n + 1 + 1) - q n := sub_pos.2 (hq (by omega))
  positivity

/-- ... and it BREAKS without monotonicity: 0, 1, -2 gives ΔA₀ = -1. -/
noncomputable def badSeq (k : ℕ) : ℚ := if k = 0 then 0 else if k = 1 then 1 else -2

example : Agen badSeq 0 - Egen badSeq 0 = -1 := by
  rw [lemma1_general]
  norm_num [badSeq]

/-! ## E. Consistency with the paper's intermediate step -/

/-- ΔAₙ = ½ gₙ (pₙ₊₂ − pₙ), the line before the telescoping in the paper's proof. -/
theorem delta_alt (n : ℕ) :
    A n - E n = gq n * ((p (n + 1 + 1) : ℚ) - p n) / 2 := by
  unfold A E gq; ring

#print axioms PrimeGaps.delta_ge_four
#print axioms PrimeGaps.naive_upper_bound_false_at_N1
#print axioms PrimeGaps.delta_pos_general
#print axioms PrimeGaps.lemma1_general
#print axioms PrimeGaps.dA0
#print axioms PrimeGaps.dA1
#print axioms PrimeGaps.dA2

end PrimeGaps
