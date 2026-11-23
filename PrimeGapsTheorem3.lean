import Mathlib
import PrimeGaps

open Finset

namespace PrimeGaps

/-! # Finite area bounds and transfer principles

1. Unconditional, exact lower bound: ∑ ΔAₙ ≥ (p_N - 2)² / (2N).
   (Telescoping + Cauchy–Schwarz; no analytic number theory needed.)
2. Transfer principle: any upper bound for the second moment ∑ gₙ²
   gives the same bound for ∑ ΔAₙ. The analytic input (Heath-Brown,
   Stadlmann, Selberg under RH) stays a hypothesis; Lean cannot supply it.
-/

/-- Telescoping: the gaps sum to p_N - p_0. -/
theorem sum_gq (N : ℕ) : ∑ n ∈ range N, gq n = (p N : ℚ) - p 0 := by
  unfold gq
  exact Finset.sum_range_sub (fun k => (p k : ℚ)) N

/-- Cauchy–Schwarz: (∑ gₙ)² ≤ N ∑ gₙ². -/
theorem sum_sq_lower (N : ℕ) :
    ((p N : ℚ) - p 0) ^ 2 ≤ (∑ n ∈ range N, gq n ^ 2) * N := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range N) gq (fun _ => (1 : ℚ))
  simpa [sum_gq] using h

/-- The cross terms are positive, so ∑ ΔAₙ ≥ ½ ∑ gₙ². -/
theorem sum_delta_ge_half (N : ℕ) :
    (∑ n ∈ range N, gq n ^ 2) / 2 ≤ ∑ n ∈ range N, (A n - E n) := by
  rw [sum_delta_eq]
  have : 0 ≤ ∑ n ∈ range N, gq n * gq (n + 1) :=
    Finset.sum_nonneg fun n _ => (mul_pos (gq_pos n) (gq_pos (n + 1))).le
  linarith

/-- Unconditional lower bound. With p_N ~ N ln N (PNT) this is ≫ N (ln N)². -/
theorem sum_delta_lower (N : ℕ) (hN : 0 < N) :
    ((p N : ℚ) - p 0) ^ 2 / (2 * N) ≤ ∑ n ∈ range N, (A n - E n) := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hN0 : (N : ℚ) ≠ 0 := hN'.ne'
  have h1 := sum_sq_lower N
  have h2 := sum_delta_ge_half N
  have h3 : ((p N : ℚ) - p 0) ^ 2 / N ≤ ∑ n ∈ range N, gq n ^ 2 := by
    rw [div_le_iff₀ hN']; exact h1
  calc ((p N : ℚ) - p 0) ^ 2 / (2 * N)
      = (((p N : ℚ) - p 0) ^ 2 / N) / 2 := by field_simp
    _ ≤ (∑ n ∈ range N, gq n ^ 2) / 2 := by linarith
    _ ≤ _ := h2

/-- Clean upper bound with no boundary fudge: ∑_{n<N} ΔAₙ ≤ ∑_{n≤N} gₙ². -/
theorem sum_delta_le_second_moment (N : ℕ) :
    ∑ n ∈ range N, (A n - E n) ≤ ∑ n ∈ range (N + 1), gq n ^ 2 := by
  have h := theorem2_corrected N
  rw [Finset.sum_range_succ]
  have := sq_nonneg (gq N)
  linarith

/-- Transfer principle: ANY second-moment bound (hypothesis `hB`) bounds ∑ ΔAₙ. -/
theorem sum_delta_le_of_bound (N : ℕ) (B : ℚ)
    (hB : ∑ n ∈ range (N + 1), gq n ^ 2 ≤ B) :
    ∑ n ∈ range N, (A n - E n) ≤ B :=
  (sum_delta_le_second_moment N).trans hB

#print axioms PrimeGaps.sum_delta_lower
#print axioms PrimeGaps.sum_delta_le_of_bound

end PrimeGaps
