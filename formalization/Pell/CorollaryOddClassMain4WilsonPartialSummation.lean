import Pell.CorollaryOddClassMain4WilsonAwayFromEight

/-!
# Finite Abel reduction for the Wilson four-twist polynomial

This module isolates the next unconditional step in Wilson's proof.  A
reciprocal sum through the exact natural endpoint `N` is written in terms of
ordinary prefix sums.  The result is finite and exact; it introduces no
analytic estimate.
-/

namespace PellPaper

open NumberTheorySymbols
open scoped BigOperators

noncomputable section

/-- The prefix through `N`, with the source indexing `1, ..., N`. -/
def main4AbelPrefix (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, a (j + 1)

@[simp]
theorem main4AbelPrefix_zero (a : ℕ → ℝ) :
    main4AbelPrefix a 0 = 0 := by
  simp [main4AbelPrefix]

theorem main4AbelPrefix_succ (a : ℕ → ℝ) (N : ℕ) :
    main4AbelPrefix a (N + 1) = main4AbelPrefix a N + a (N + 1) := by
  simp [main4AbelPrefix, Finset.sum_range_succ]

/-- The range presentation is exactly the source interval `1, ..., N`. -/
theorem main4AbelPrefix_eq_sum_Icc (a : ℕ → ℝ) (N : ℕ) :
    main4AbelPrefix a N = ∑ n ∈ Finset.Icc 1 N, a n := by
  unfold main4AbelPrefix
  rw [← Finset.Ico_add_one_right_eq_Icc 1 N,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

/-- Exact discrete Abel summation for reciprocal weights.  The endpoint is
`k + 1`, so every denominator is positive and no zero convention enters. -/
theorem sum_range_reciprocal_eq_main4AbelPrefix (a : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), a (j + 1) / ((j + 1 : ℕ) : ℝ)) =
      main4AbelPrefix a (k + 1) / ((k + 1 : ℕ) : ℝ) +
        ∑ j ∈ Finset.range k,
          main4AbelPrefix a (j + 1) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
  induction k with
  | zero =>
      simp [main4AbelPrefix]
  | succ k ih =>
      have halgebra (A b : ℝ) :
          A / ((k + 1 : ℕ) : ℝ) + b / ((k + 2 : ℕ) : ℝ) =
            (A + b) / ((k + 2 : ℕ) : ℝ) +
              A / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
        norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        field_simp
        ring
      have hprefix :
          main4AbelPrefix a (k + 2) =
            main4AbelPrefix a (k + 1) + a (k + 2) := by
        simpa only [Nat.add_assoc] using main4AbelPrefix_succ a (k + 1)
      calc
        (∑ j ∈ Finset.range (k.succ + 1),
            a (j + 1) / ((j + 1 : ℕ) : ℝ)) =
            (∑ j ∈ Finset.range (k + 1),
              a (j + 1) / ((j + 1 : ℕ) : ℝ)) +
                a (k + 2) / ((k + 2 : ℕ) : ℝ) := by
          rw [show k.succ + 1 = (k + 1) + 1 by omega,
            Finset.sum_range_succ]
        _ =
            (main4AbelPrefix a (k + 1) / ((k + 1 : ℕ) : ℝ) +
              ∑ j ∈ Finset.range k,
                main4AbelPrefix a (j + 1) /
                  (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))) +
              a (k + 2) / ((k + 2 : ℕ) : ℝ) := by
          rw [ih]
        _ =
            (main4AbelPrefix a (k + 2) / ((k + 2 : ℕ) : ℝ)) +
              ((∑ j ∈ Finset.range k,
                main4AbelPrefix a (j + 1) /
                  (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))) +
                main4AbelPrefix a (k + 1) /
                  (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))) := by
          rw [hprefix]
          linarith [halgebra (main4AbelPrefix a (k + 1)) (a (k + 2))]
        _ =
            main4AbelPrefix a (k.succ + 1) / ((k.succ + 1 : ℕ) : ℝ) +
              ∑ j ∈ Finset.range k.succ,
                main4AbelPrefix a (j + 1) /
                  (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
          rw [Finset.sum_range_succ]

/-! ## Application to one fixed Wilson twist -/

/-- The unweighted Jacobi coefficient before the reciprocal factor. -/
def main4WilsonTwistCoefficient
    (rho : DirichletCharacter ℤ 8) (m n : ℕ) : ℝ :=
  (rho (n : ZMod 8) : ℝ) * (J((n : ℤ) | m) : ℝ)

/-- The finite reciprocal polynomial in range coordinates. -/
theorem main4TwistedJacobiReciprocalPolynomial_eq_sum_range
    (rho : DirichletCharacter ℤ 8) (m N : ℕ) :
    main4TwistedJacobiReciprocalPolynomial rho m N =
      ∑ j ∈ Finset.range N,
        main4WilsonTwistCoefficient rho m (j + 1) /
          ((j + 1 : ℕ) : ℝ) := by
  unfold main4TwistedJacobiReciprocalPolynomial
  rw [← main4AbelPrefix_eq_sum_Icc]
  unfold main4AbelPrefix main4WilsonTwistCoefficient
  rfl

/-- An ordinary (non-harmonic) prefix summed over an arbitrary finite
radicand family and arbitrary real weights. -/
def main4WilsonWeightedTwistPrefix
    (rho : DirichletCharacter ℤ 8) (weight : ℕ → ℝ)
    (s : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ m ∈ s, weight m *
    ∑ n ∈ Finset.Icc 1 N, main4WilsonTwistCoefficient rho m n

/-- Summing a coefficient first in `n` or first in `m` gives the same
ordinary prefix. -/
theorem main4AbelPrefix_sum_weightedTwistCoefficient
    (rho : DirichletCharacter ℤ 8) (weight : ℕ → ℝ)
    (s : Finset ℕ) (N : ℕ) :
    main4AbelPrefix
        (fun n ↦ ∑ m ∈ s,
          weight m * main4WilsonTwistCoefficient rho m n) N =
      main4WilsonWeightedTwistPrefix rho weight s N := by
  rw [main4AbelPrefix_eq_sum_Icc]
  unfold main4WilsonWeightedTwistPrefix
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Fubini converts a weighted family of reciprocal polynomials into one
reciprocal sum whose coefficients are the ordinary bilinear prefixes. -/
theorem sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_range
    (rho : DirichletCharacter ℤ 8) (weight : ℕ → ℝ)
    (s : Finset ℕ) (N : ℕ) :
    (∑ m ∈ s, weight m *
        main4TwistedJacobiReciprocalPolynomial rho m N) =
      ∑ j ∈ Finset.range N,
        (∑ m ∈ s, weight m *
          main4WilsonTwistCoefficient rho m (j + 1)) /
            ((j + 1 : ℕ) : ℝ) := by
  calc
    (∑ m ∈ s, weight m *
        main4TwistedJacobiReciprocalPolynomial rho m N) =
        ∑ m ∈ s, ∑ j ∈ Finset.range N,
          weight m *
            (main4WilsonTwistCoefficient rho m (j + 1) /
              ((j + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [main4TwistedJacobiReciprocalPolynomial_eq_sum_range,
        Finset.mul_sum]
    _ = ∑ j ∈ Finset.range N, ∑ m ∈ s,
          weight m *
            (main4WilsonTwistCoefficient rho m (j + 1) /
              ((j + 1 : ℕ) : ℝ)) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range N,
        (∑ m ∈ s, weight m *
          main4WilsonTwistCoefficient rho m (j + 1)) /
            ((j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      ring

/-- Exact finite partial summation for one weighted Wilson twist. -/
theorem sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel
    (rho : DirichletCharacter ℤ 8) (weight : ℕ → ℝ)
    (s : Finset ℕ) (k : ℕ) :
    (∑ m ∈ s, weight m *
        main4TwistedJacobiReciprocalPolynomial rho m (k + 1)) =
      main4WilsonWeightedTwistPrefix rho weight s (k + 1) /
          ((k + 1 : ℕ) : ℝ) +
        ∑ j ∈ Finset.range k,
          main4WilsonWeightedTwistPrefix rho weight s (j + 1) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
  rw [sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_range,
    sum_range_reciprocal_eq_main4AbelPrefix
      (fun n ↦ ∑ m ∈ s,
        weight m * main4WilsonTwistCoefficient rho m n) k,
    main4AbelPrefix_sum_weightedTwistCoefficient]
  apply congrArg (fun x ↦
    main4WilsonWeightedTwistPrefix rho weight s (k + 1) /
        ((k + 1 : ℕ) : ℝ) + x)
  apply Finset.sum_congr rfl
  intro j _
  rw [main4AbelPrefix_sum_weightedTwistCoefficient]

/-- Positive-endpoint form of the preceding identity. -/
theorem sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel_of_pos
    (rho : DirichletCharacter ℤ 8) (weight : ℕ → ℝ)
    (s : Finset ℕ) (N : ℕ) (hN : 0 < N) :
    (∑ m ∈ s, weight m *
        main4TwistedJacobiReciprocalPolynomial rho m N) =
      main4WilsonWeightedTwistPrefix rho weight s N / (N : ℝ) +
        ∑ j ∈ Finset.range (N - 1),
          main4WilsonWeightedTwistPrefix rho weight s (j + 1) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel
      rho weight s k

/-! ## Exact Abel decomposition of the four source branches -/

/-- The four ordinary bilinear prefixes matching the away-from-eight
radicand families and divisor weights. -/
def main4WilsonFourTwistPrefixSumAwayFromEight (X : ℝ) (N : ℕ) : ℝ :=
  main4WilsonWeightedTwistPrefix 1
      (fun m ↦ 1 / (m.divisors.card : ℝ))
      (main4OddBranchRadicandsBelow X) N +
  main4WilsonWeightedTwistPrefix main4ChiFourModuloEight
      (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
      (main4FourBranchRadicandsBelow X) N +
  main4WilsonWeightedTwistPrefix ZMod.χ₈
      (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
      (main4EightOneBranchRadicandsBelowAwayFromEight X) N +
  main4WilsonWeightedTwistPrefix ZMod.χ₈'
      (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
      (main4EightThreeBranchRadicandsBelow X) N

/-- Wilson's four-twist reciprocal polynomial is exactly the terminal
prefix plus the finite Abel kernel applied to ordinary bilinear prefixes.
The source endpoint remains `ceil(X)^2`. -/
theorem main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight_eq_abel
    {X : ℝ} (hX : 0 < X) :
    let N := ⌈X⌉₊ ^ 2
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X =
      main4WilsonFourTwistPrefixSumAwayFromEight X N / (N : ℝ) +
        ∑ j ∈ Finset.range (N - 1),
          main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
  let N := ⌈X⌉₊ ^ 2
  have hceil : 0 < ⌈X⌉₊ := Nat.ceil_pos.mpr hX
  have hN : 0 < N := pow_pos hceil 2
  have hodd :=
    sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel_of_pos
      (1 : DirichletCharacter ℤ 8)
      (fun m ↦ 1 / (m.divisors.card : ℝ))
      (main4OddBranchRadicandsBelow X) N hN
  have hfour :=
    sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel_of_pos
      main4ChiFourModuloEight
      (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
      (main4FourBranchRadicandsBelow X) N hN
  have heightOne :=
    sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel_of_pos
      ZMod.χ₈
      (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
      (main4EightOneBranchRadicandsBelowAwayFromEight X) N hN
  have heightThree :=
    sum_weight_mul_main4TwistedJacobiReciprocalPolynomial_eq_abel_of_pos
      ZMod.χ₈'
      (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
      (main4EightThreeBranchRadicandsBelow X) N hN
  change main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X =
    main4WilsonFourTwistPrefixSumAwayFromEight X N / (N : ℝ) +
      ∑ j ∈ Finset.range (N - 1),
        main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1) /
          (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))
  unfold main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight
  dsimp only
  rw [hodd, hfour, heightOne, heightThree]
  unfold main4WilsonFourTwistPrefixSumAwayFromEight
  simp_rw [add_div]
  simp only [Finset.sum_add_distrib]
  ring

/-- The positive Abel majorant left after the exact finite identity. -/
def main4WilsonFourTwistAbelMajorantAwayFromEight (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  |main4WilsonFourTwistPrefixSumAwayFromEight X N| / (N : ℝ) +
    ∑ j ∈ Finset.range (N - 1),
      |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
        (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))

/-- The signed four-twist polynomial is bounded above by its ordinary-prefix
Abel majorant.  This is the exact point where Wilson's rectangle estimates
enter; everything before this theorem is unconditional finite algebra. -/
theorem main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight_le_abelMajorant
    {X : ℝ} (hX : 0 < X) :
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X ≤
      main4WilsonFourTwistAbelMajorantAwayFromEight X := by
  let N := ⌈X⌉₊ ^ 2
  rw [main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight_eq_abel hX]
  change
    main4WilsonFourTwistPrefixSumAwayFromEight X N / (N : ℝ) +
        (∑ j ∈ Finset.range (N - 1),
          main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))) ≤
      |main4WilsonFourTwistPrefixSumAwayFromEight X N| / (N : ℝ) +
        ∑ j ∈ Finset.range (N - 1),
          |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))
  apply add_le_add
  · exact div_le_div_of_nonneg_right (le_abs_self _)
      (Nat.cast_nonneg N)
  · apply Finset.sum_le_sum
    intro j _
    exact div_le_div_of_nonneg_right (le_abs_self _)
      (mul_nonneg (Nat.cast_nonneg (j + 1)) (Nat.cast_nonneg (j + 2)))


end

end PellPaper
