import Pell.PrimitiveSourceLinearFibre

/-!
# Primitive integral representatives of rational projective slopes

The key `none` represents infinity. The cardinality bound concerns target
vectors, not source-target pairs or solutions of a fixed norm equation.
-/

namespace PellPaper
noncomputable section

/-- The rational slope of an integral binary vector, including infinity.
The zero vector is also assigned `none`; primitivity is required only by
the representative and cardinality results below. -/
def integralBinarySlope (y : Fin 2 → ℤ) : Option ℚ :=
  if y 1 = 0 then none else some ((y 0 : ℚ) / (y 1 : ℚ))

/-- Equal slope keys imply vanishing cross determinant, with both axis
cases included and without dividing by an integer. -/
theorem cross_eq_zero_of_integralBinarySlope_eq
    (y z : Fin 2 → ℤ) (h : integralBinarySlope y = integralBinarySlope z) :
    z 0 * (-y 1) + z 1 * y 0 = 0 := by
  by_cases hy : y 1 = 0
  · by_cases hz : z 1 = 0
    · simp [hy, hz]
    · simp [integralBinarySlope, hy, hz] at h
  · by_cases hz : z 1 = 0
    · simp [integralBinarySlope, hy, hz] at h
    · have heq : (y 0 : ℚ) / (y 1 : ℚ) = (z 0 : ℚ) / (z 1 : ℚ) := by
        simpa [integralBinarySlope, hy, hz] using h
      have hyQ : (y 1 : ℚ) ≠ 0 := by exact_mod_cast hy
      have hzQ : (z 1 : ℚ) ≠ 0 := by exact_mod_cast hz
      have hcross : y 0 * z 1 = z 0 * y 1 := by
        exact_mod_cast (div_eq_div_iff hyQ hzQ).mp heq
      nlinarith

/-- A primitive integral vector has at most the two signed primitive
representatives of its rational projective slope. -/
theorem primitive_eq_or_neg_of_integralBinarySlope_eq
    (y z : Fin 2 → ℤ) (hy : IsCoprime (y 0) (y 1))
    (hz : IsCoprime (z 0) (z 1))
    (h : integralBinarySlope y = integralBinarySlope z) :
    z = y ∨ z = -y := by
  refine primitive_linear_solutions_eq_or_neg (-y 1) (y 0) ?_ y z hy hz ?_ ?_
  · rcases hy.ne_zero_or_ne_zero with h0 | h1
    · exact Or.inr h0
    · exact Or.inl (neg_ne_zero.mpr h1)
  · ring
  · exact cross_eq_zero_of_integralBinarySlope_eq y z h

/-- Each slope fibre in a finite family of primitive integral vectors
has cardinality at most two, including the infinity fibre. -/
theorem card_integralBinarySlope_fibre_le_two
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ y ∈ S, IsCoprime (y 0) (y 1)) (r : Option ℚ) :
    (S.filter fun y => integralBinarySlope y = r).card ≤ 2 := by
  classical
  let U := S.filter fun y => integralBinarySlope y = r
  rcases U.eq_empty_or_nonempty with hU | ⟨y, hy⟩
  · change U.card ≤ 2
    simp [hU]
  · have hy' := Finset.mem_filter.mp hy
    apply card_primitive_linear_solutions_le_two (-y 1) (y 0)
    · rcases (hS y hy'.1).ne_zero_or_ne_zero with h0 | h1
      · exact Or.inr h0
      · exact Or.inl (neg_ne_zero.mpr h1)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact ⟨hS z hz'.1, cross_eq_zero_of_integralBinarySlope_eq y z
        (hy'.2.trans hz'.2.symm)⟩

/-- Counting slopes loses at most the two signs. This is a bound on a
finite set of primitive vectors, with no bounded-coordinate hypothesis. -/
theorem card_primitive_vectors_le_two_mul_card_slopes
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ y ∈ S, IsCoprime (y 0) (y 1)) :
    S.card ≤ 2 * (S.image integralBinarySlope).card := by
  classical
  calc
    S.card = ∑ r ∈ S.image integralBinarySlope,
        (S.filter fun y => integralBinarySlope y = r).card :=
      Finset.card_eq_sum_card_image integralBinarySlope S
    _ ≤ ∑ _ ∈ S.image integralBinarySlope, 2 :=
      Finset.sum_le_sum (fun r _ => card_integralBinarySlope_fibre_le_two S hS r)
    _ = _ := by simp [mul_comm]

end
end PellPaper
