import PrimeGaps
import PrimeGaps.Verification
import PrimeGapsTheorem3
import PrimeTrapezoidPick

/-! Axiom audit for the trapezoid paper's formalized results. -/

-- Lemma 1
#print axioms PrimeGaps.lemma1
#print axioms PrimeGaps.delta_alt
#print axioms PrimeGaps.sum_delta_eq

-- Proposition 2
#print axioms PrimeGaps.delta_pos
#print axioms PrimeGaps.gap_even
#print axioms PrimeGaps.delta_even
#print axioms PrimeGaps.delta_ge_four

-- Theorem 3
#print axioms PrimeGaps.sum_delta_ge_half
#print axioms PrimeGaps.theorem2_corrected
#print axioms PrimeGaps.sum_delta_lower

-- Theorem 4
#print axioms PrimeTrapezoidPick.twoI_of_g_eq_two
#print axioms PrimeTrapezoidPick.not_both_gaps_two
#print axioms PrimeTrapezoidPick.twoI_ge_fourteen_of_g_ge_four
#print axioms PrimeTrapezoidPick.twoI_ge_two
#print axioms PrimeTrapezoidPick.twoI_eq_four_iff
#print axioms PrimeTrapezoidPick.twoI_eq_fourteen_iff
#print axioms PrimeTrapezoidPick.twoI_zero
#print axioms PrimeTrapezoidPick.twoI_one
#print axioms PrimeTrapezoidPick.twoI_ge_four

-- Theorem 5 (eq. 6)
#print axioms PrimeTrapezoidPick.sum_B_eq
#print axioms PrimeTrapezoidPick.sum_B_le

-- Direct interior-point formula
#print axioms PrimeTrapezoidPick.interiorPoints
#print axioms PrimeTrapezoidPick.card_slice
#print axioms PrimeTrapezoidPick.floor_pair
#print axioms PrimeTrapezoidPick.two_mul_card_interiorPoints

-- Concrete decide checks for Q_3 and Q_4 (Figure 1)
example : (PrimeTrapezoidPick.interiorPoints 2 4).card = 2 := by decide
example : (PrimeTrapezoidPick.interiorPoints 4 2).card = 7 := by decide

-- Definitional bridge between the two prime/gap namespaces
example (n : ℕ) : PrimeGaps.p n = PrimeTrapezoidPick.p n := rfl
example (n : ℕ) : PrimeGaps.g n = PrimeTrapezoidPick.g n := rfl

-- Concrete kernel checks matching Q_3 and Q_4 in Figure 1 (no native_decide)
theorem card_interiorPoints_2_4 :
    (PrimeTrapezoidPick.interiorPoints 2 4).card = 2 := by
  decide

theorem card_interiorPoints_4_2 :
    (PrimeTrapezoidPick.interiorPoints 4 2).card = 7 := by
  decide

-- Definitional bridge between PrimeGaps and PrimeTrapezoidPick
theorem p_eq (n : ℕ) : PrimeTrapezoidPick.p n = PrimeGaps.p n := rfl
theorem g_eq (n : ℕ) : PrimeTrapezoidPick.g n = PrimeGaps.g n := rfl

#check card_interiorPoints_2_4
#check card_interiorPoints_4_2
#check p_eq
#check g_eq

#print axioms card_interiorPoints_2_4
#print axioms card_interiorPoints_4_2
#print axioms p_eq
#print axioms g_eq
