import Pell.WilsonNeutralizerCorrelation

/-!
# Neutralizer correlations controlled by coefficient mass

Selberg's Lambda-squared upper weights need not be individually bounded by
one.  The denominator-character argument only uses the sum of the absolute
weighted coefficients.  This module records that more flexible form of the
nonsquare estimate.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The absolute coefficient mass naturally occurring after expanding the
reciprocal-divisor neutralizer. -/
def main4WilsonNeutralizerCoefficientMass
    (P : ℕ) (lambdaPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ P.divisors,
    |lambdaPlus d| * main4WilsonReciprocalDivisorComplementWeight d

theorem main4WilsonNeutralizerCoefficientMass_nonneg
    (P : ℕ) (lambdaPlus : ℕ → ℝ) :
    0 ≤ main4WilsonNeutralizerCoefficientMass P lambdaPlus := by
  unfold main4WilsonNeutralizerCoefficientMass
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (abs_nonneg _)
    (main4WilsonReciprocalDivisorComplementWeight_nonneg d)

private theorem abs_jacobiSym_cast_le_one
    (q : ℤ) (d : ℕ) : |(jacobiSym q d : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy q d with h | h | h <;> rw [h] <;> norm_num

/-- Triangle inequality for an odd neutralizer, retaining the exact absolute
coefficient mass instead of assuming every upper coefficient is at most one. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_le_coefficientMass_mul
    (P M q : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hprefix : ∀ X : ℕ,
      |∑ k ∈ (Finset.Icc 1 X).filter Odd,
        (jacobiSym (q : ℤ) k : ℝ)| ≤ B) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M q| ≤
      main4WilsonNeutralizerCoefficientMass P lambdaPlus * B := by
  rw [wilsonJacobiCorrelation_oddNeutralizer_eq_divisor_prefix_sum
    P M q hP hPodd lambdaPlus]
  calc
    |∑ d ∈ P.divisors,
        (lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) d : ℝ) *
          (∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
            (jacobiSym (q : ℤ) k : ℝ))| ≤
        ∑ d ∈ P.divisors,
          |(lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d) *
            (jacobiSym (q : ℤ) d : ℝ) *
            (∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
              (jacobiSym (q : ℤ) k : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.divisors,
          (|lambdaPlus d| *
            main4WilsonReciprocalDivisorComplementWeight d) * B := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg
          (main4WilsonReciprocalDivisorComplementWeight_nonneg d)]
      have hj := abs_jacobiSym_cast_le_one (q : ℤ) d
      have hpref := hprefix (M / d)
      have hcoeff :
          0 ≤ |lambdaPlus d| *
            main4WilsonReciprocalDivisorComplementWeight d :=
        mul_nonneg (abs_nonneg _)
          (main4WilsonReciprocalDivisorComplementWeight_nonneg d)
      calc
        |lambdaPlus d| *
              main4WilsonReciprocalDivisorComplementWeight d *
            |(jacobiSym (q : ℤ) d : ℝ)| *
            |∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
              (jacobiSym (q : ℤ) k : ℝ)| ≤
            (|lambdaPlus d| *
              main4WilsonReciprocalDivisorComplementWeight d * 1) *
              |∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
                (jacobiSym (q : ℤ) k : ℝ)| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hj hcoeff) (abs_nonneg _)
        _ ≤
            |lambdaPlus d| *
              main4WilsonReciprocalDivisorComplementWeight d * 1 * B := by
          exact mul_le_mul_of_nonneg_left hpref (mul_nonneg hcoeff (by norm_num))
        _ = (|lambdaPlus d| *
              main4WilsonReciprocalDivisorComplementWeight d) * B := by
          ring
    _ = main4WilsonNeutralizerCoefficientMass P lambdaPlus * B := by
      unfold main4WilsonNeutralizerCoefficientMass
      rw [Finset.sum_mul]

/-- Pólya--Vinogradov supplies the coefficient-mass version of the nonsquare
correlation bound. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_le_coefficientMass
    (P M q : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ)
    (hq : 0 < q) (hqodd : Odd q) (hqsquare : ¬ IsSquare q) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M q| ≤
      main4WilsonNeutralizerCoefficientMass P lambdaPlus *
        (2 * Real.sqrt (4 * (q : ℝ)) *
          (1 + Real.log (4 * (q : ℝ)))) := by
  have hlog : 0 ≤ Real.log (4 * (q : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 4 * q by omega)
  apply abs_wilsonJacobiCorrelation_oddNeutralizer_le_coefficientMass_mul
    P M q hP hPodd lambdaPlus
      (2 * Real.sqrt (4 * (q : ℝ)) *
        (1 + Real.log (4 * (q : ℝ)))) (by positivity)
  intro X
  exact abs_sum_jacobiSym_denominator_odd_le q X hq hqodd hqsquare

/-- Uniform form for a product of two numerator variables in `[1,N]`. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_mul_le_coefficientMass
    (P M n₁ n₂ N : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hn₁N : n₁ ≤ N) (hn₂N : n₂ ≤ N)
    (hodd : Odd (n₁ * n₂)) (hns : ¬ IsSquare (n₁ * n₂)) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n₁ * n₂)| ≤
      main4WilsonNeutralizerCoefficientMass P lambdaPlus *
        (4 * (N : ℝ) *
          (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by
  have hN : 0 < N := hn₁.trans_le hn₁N
  have harg :
      4 * ((n₁ * n₂ : ℕ) : ℝ) ≤ (2 * (N : ℝ)) ^ 2 := by
    exact_mod_cast (show 4 * (n₁ * n₂) ≤ (2 * N) ^ 2 by
      nlinarith [Nat.mul_le_mul hn₁N hn₂N])
  have hsqrt :
      Real.sqrt (4 * ((n₁ * n₂ : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, harg⟩
  have hlog :
      Real.log (4 * ((n₁ * n₂ : ℕ) : ℝ)) ≤
        Real.log ((2 * (N : ℝ)) ^ 2) :=
    Real.log_le_log (by positivity) harg
  have hlogLeft :
      0 ≤ 1 + Real.log (4 * ((n₁ * n₂ : ℕ) : ℝ)) := by
    have : 0 ≤ Real.log (4 * ((n₁ * n₂ : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 4 * (n₁ * n₂) from
        Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by norm_num) (Nat.mul_ne_zero hn₁.ne' hn₂.ne')))
    linarith
  have hmass := main4WilsonNeutralizerCoefficientMass_nonneg P lambdaPlus
  have hc := abs_wilsonJacobiCorrelation_oddNeutralizer_le_coefficientMass
    P M (n₁ * n₂) hP hPodd lambdaPlus
      (Nat.mul_pos hn₁ hn₂) hodd hns
  calc
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n₁ * n₂)| ≤
        main4WilsonNeutralizerCoefficientMass P lambdaPlus *
          (2 * Real.sqrt (4 * ((n₁ * n₂ : ℕ) : ℝ)) *
            (1 + Real.log (4 * ((n₁ * n₂ : ℕ) : ℝ)))) := hc
    _ ≤ main4WilsonNeutralizerCoefficientMass P lambdaPlus *
          (2 * (2 * (N : ℝ)) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by
      gcongr
    _ = main4WilsonNeutralizerCoefficientMass P lambdaPlus *
          (4 * (N : ℝ) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by ring

/-- Complete nonsquare aggregate with its dependence on the absolute
neutralizer coefficient mass made explicit. -/
theorem abs_sum_nonsquare_wilsonOddNeutralizerCorrelation_le_coefficientMass
    (a : ℕ → ℝ) (P M N : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ)
    (ha : main4OddSupportedUnitBound a) :
    |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun p ↦ ¬ IsSquare (p.1 * p.2)),
      a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
          (p.1 * p.2)| ≤
      (N : ℝ) ^ 2 *
        (main4WilsonNeutralizerCoefficientMass P lambdaPlus *
          (4 * (N : ℝ) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2)))) := by
  classical
  let S := ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p ↦ ¬ IsSquare (p.1 * p.2))
  let B := main4WilsonNeutralizerCoefficientMass P lambdaPlus *
    (4 * (N : ℝ) * (1 + Real.log ((2 * (N : ℝ)) ^ 2)))
  have hB : 0 ≤ B := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp [B]
    · have hlog : 0 ≤ Real.log ((2 * (N : ℝ)) ^ 2) := by
        apply Real.log_nonneg
        have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hNpos]
      dsimp [B]
      exact mul_nonneg
        (main4WilsonNeutralizerCoefficientMass_nonneg P lambdaPlus)
        (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg N))
          (by linarith))
  have hpoint (p : ℕ × ℕ) (hp : p ∈ S) :
      |a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
          (p.1 * p.2)| ≤ B := by
    obtain ⟨hpbox, hns⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpbox
    obtain ⟨hp₁pos, hp₁N⟩ := Finset.mem_Icc.mp hp₁
    obtain ⟨hp₂pos, hp₂N⟩ := Finset.mem_Icc.mp hp₂
    by_cases hp₁even : Even p.1
    · rw [ha.1 p.1 hp₁even]
      simp [hB]
    · by_cases hp₂even : Even p.2
      · rw [ha.1 p.2 hp₂even]
        simp [hB]
      · have hp₁odd : Odd p.1 := Nat.not_even_iff_odd.mp hp₁even
        have hp₂odd : Odd p.2 := Nat.not_even_iff_odd.mp hp₂even
        have hc :=
          abs_wilsonJacobiCorrelation_oddNeutralizer_mul_le_coefficientMass
            P M p.1 p.2 N hP hPodd lambdaPlus
              hp₁pos hp₂pos hp₁N hp₂N (hp₁odd.mul hp₂odd) hns
        dsimp [B]
        calc
          |a p.1 * a p.2 *
              wilsonJacobiCorrelation
                (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
                (p.1 * p.2)| =
              |a p.1| * |a p.2| *
                |wilsonJacobiCorrelation
                  (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
                  (p.1 * p.2)| := by simp only [abs_mul]
          _ ≤ 1 * 1 *
              (main4WilsonNeutralizerCoefficientMass P lambdaPlus *
                (4 * (N : ℝ) *
                  (1 + Real.log ((2 * (N : ℝ)) ^ 2)))) := by
            gcongr
            · exact ha.2 p.1
            · exact ha.2 p.2
          _ = main4WilsonNeutralizerCoefficientMass P lambdaPlus *
                (4 * (N : ℝ) *
                  (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by ring
  calc
    |∑ p ∈ S,
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤
        ∑ p ∈ S,
          |a p.1 * a p.2 *
            wilsonJacobiCorrelation
              (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
              (p.1 * p.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, B := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * B := by simp
    _ ≤ (N : ℝ) ^ 2 * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hcardNat : S.card ≤ N ^ 2 := by
        calc
          S.card ≤
              ((Finset.Icc 1 N).product (Finset.Icc 1 N)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = N ^ 2 := by simp [pow_two]
      exact_mod_cast hcardNat
    _ = (N : ℝ) ^ 2 *
        (main4WilsonNeutralizerCoefficientMass P lambdaPlus *
          (4 * (N : ℝ) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2)))) := by
      rfl

end

end PellPaper
