import Pell.WilsonOddNeutralizerSquareAggregate

/-!
# Wilson's square neutralizer aggregate from one total-mass bound

For the square part of Wilson's expanded neutralizer moment, the full
coprime form of the upper-sieve estimate is unnecessary.  A square Jacobi
symbol is a zero-one coprimality indicator, while an upper-Moebius
neutralizer is pointwise nonnegative.  Consequently every square correlation
is bounded by the same total neutralizer mass.  This file records that finite
reduction and leaves only a single total-mass estimate for the chosen sieve
coefficients.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Total mass of Wilson's (unmasked) neutralizer on `[1,M]`. -/
def main4WilsonNeutralizerTotalMass
    (P M : ℕ) (lambdaPlus : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    main4WilsonNeutralizerMajorant P lambdaPlus m

theorem main4WilsonNeutralizerTotalMass_nonneg
    (P M : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    0 ≤ main4WilsonNeutralizerTotalMass P M lambdaPlus := by
  unfold main4WilsonNeutralizerTotalMass
  apply Finset.sum_nonneg
  intro m hm
  exact (main4WilsonReciprocalDivisorWeight_nonneg m).trans
    (main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
      P m hP (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1) lambdaPlus hUpper)

theorem main4WilsonReciprocalDivisorCoprimeSieveSum_nonneg
    (P M n : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    0 ≤ main4WilsonReciprocalDivisorCoprimeSieveSum
      P M n lambdaPlus := by
  rw [← sum_main4WilsonNeutralizerMajorant_coprimeIndicator_eq_sieveSum
    P M n hP.ne_zero lambdaPlus]
  apply Finset.sum_nonneg
  intro m hm
  have hmajor : 0 ≤ main4WilsonNeutralizerMajorant P lambdaPlus m :=
    (main4WilsonReciprocalDivisorWeight_nonneg m).trans
      (main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
        P m hP (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1) lambdaPlus hUpper)
  positivity

/-- Removing a coprimality indicator can only increase the mass of the
nonnegative neutralizer. -/
theorem main4WilsonReciprocalDivisorCoprimeSieveSum_le_totalMass
    (P M n : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    main4WilsonReciprocalDivisorCoprimeSieveSum P M n lambdaPlus ≤
      main4WilsonNeutralizerTotalMass P M lambdaPlus := by
  rw [← sum_main4WilsonNeutralizerMajorant_coprimeIndicator_eq_sieveSum
    P M n hP.ne_zero lambdaPlus]
  unfold main4WilsonNeutralizerTotalMass
  apply Finset.sum_le_sum
  intro m hm
  have hmajor : 0 ≤ main4WilsonNeutralizerMajorant P lambdaPlus m :=
    (main4WilsonReciprocalDivisorWeight_nonneg m).trans
      (main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
        P m hP (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1) lambdaPlus hUpper)
  by_cases hcop : m.Coprime n
  · rw [if_pos hcop, mul_one]
  · simp [hcop, hmajor]

/-- Every square correlation of the odd neutralizer is bounded by its one
unrestricted total mass. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_sq_le_totalMass
    (P M n : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n ^ 2)| ≤
      main4WilsonNeutralizerTotalMass P M lambdaPlus := by
  rw [abs_of_nonneg
    (wilsonJacobiCorrelation_oddNeutralizer_sq_nonneg
      P M n hP lambdaPlus hUpper)]
  exact
    (wilsonJacobiCorrelation_oddNeutralizer_sq_le_abs_sieveSum
      P M n hP lambdaPlus hUpper).trans <| by
        rw [abs_of_nonneg
          (main4WilsonReciprocalDivisorCoprimeSieveSum_nonneg
            P M n hP lambdaPlus hUpper)]
        exact main4WilsonReciprocalDivisorCoprimeSieveSum_le_totalMass
          P M n hP lambdaPlus hUpper

/-- The complete square aggregate follows from one total neutralizer-mass
bound and the elementary count of square-product pairs. -/
theorem abs_sum_square_wilsonOddNeutralizerCorrelation_le_of_totalMass
    (a : ℕ → ℝ) (P M N : ℕ) (lambdaPlus : ℕ → ℝ) (B : ℝ)
    (hP : Squarefree P)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (ha : ∀ n : ℕ, |a n| ≤ 1)
    (hmass : main4WilsonNeutralizerTotalMass P M lambdaPlus ≤ B) :
    |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun p ↦ IsSquare (p.1 * p.2)),
      a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
          (p.1 * p.2)| ≤
      B * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by
  have hB : 0 ≤ B :=
    (main4WilsonNeutralizerTotalMass_nonneg
      P M hP lambdaPlus hUpper).trans hmass
  rw [show ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p ↦ IsSquare (p.1 * p.2)) = squareProductPairsUpTo N by rfl]
  calc
    |∑ p ∈ squareProductPairsUpTo N,
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤
        ∑ p ∈ squareProductPairsUpTo N,
          |a p.1 * a p.2 *
            wilsonJacobiCorrelation
              (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
              (p.1 * p.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ squareProductPairsUpTo N, B := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨_hpBox, hpSquare⟩ := Finset.mem_filter.mp hp
      obtain ⟨r, hr⟩ :=
        (isSquare_iff_exists_sq (p.1 * p.2)).mp hpSquare
      have hcorr :=
        abs_wilsonJacobiCorrelation_oddNeutralizer_sq_le_totalMass
          P M r hP lambdaPlus hUpper
      have hcorr' :
          |wilsonJacobiCorrelation
              (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
              (p.1 * p.2)| ≤
            main4WilsonNeutralizerTotalMass P M lambdaPlus := by
        simpa only [hr] using hcorr
      calc
        |a p.1 * a p.2 *
            wilsonJacobiCorrelation
              (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
              (p.1 * p.2)| =
            |a p.1| * |a p.2| *
              |wilsonJacobiCorrelation
                (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
                (p.1 * p.2)| := by simp only [abs_mul]
        _ ≤ 1 * 1 * B := by
          gcongr
          · exact ha p.1
          · exact ha p.2
          · exact hcorr'.trans hmass
        _ = B := by ring
    _ = B * (squareProductPairsUpTo N).card := by
      simp [mul_comm]
    _ ≤ B * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (card_squareProductPairsUpTo_cast_le N) hB

end

end PellPaper
