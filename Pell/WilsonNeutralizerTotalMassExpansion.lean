import Pell.WilsonOddNeutralizerSquareTotalMass
import Pell.WilsonNeutralizerCorrelationCoefficientMass

/-!
# Exact floor expansion of Wilson's neutralizer mass

This module separates the finite endpoint error from the Selberg main sum.
For arbitrary upper coefficients, the total neutralizer mass equals a divisor
sum with `floor(M/d)`.  Replacing that floor by `M/d` costs at most the
absolute complementary coefficient mass.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

private theorem card_Icc_filter_dvd_eq_div (M d : ℕ) :
    ((Finset.Icc 1 M).filter (fun m ↦ d ∣ m)).card = M / d := by
  have hset :
      Finset.Icc 1 M =
        (Finset.range M.succ).filter (fun m ↦ m ≠ 0) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.filter_filter]
  simpa only [and_assoc] using Nat.card_multiples' M d

private theorem abs_natCast_div_sub_div_le_one
    (M d : ℕ) (hd : 0 < d) :
    |((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)| ≤ 1 := by
  have hlower : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hupper :
      (M : ℝ) / (d : ℝ) < ((M / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hd)]
    exact_mod_cast (show M < (M / d + 1) * d by
      simpa [Nat.mul_comm] using Nat.lt_mul_div_succ M hd)
  rw [abs_of_nonpos (sub_nonpos.mpr hlower)]
  linarith

/-- Exact divisor-first expansion of the unrestricted neutralizer mass. -/
theorem main4WilsonNeutralizerTotalMass_eq_sum_natDiv
    (P M : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ) :
    main4WilsonNeutralizerTotalMass P M lambdaPlus =
      ∑ d ∈ P.divisors,
        lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
          ((M / d : ℕ) : ℝ) := by
  calc
    main4WilsonNeutralizerTotalMass P M lambdaPlus =
        main4WilsonReciprocalDivisorCoprimeSieveSum
          P M 1 lambdaPlus := by
      rw [← sum_main4WilsonNeutralizerMajorant_coprimeIndicator_eq_sieveSum
        P M 1 hP lambdaPlus]
      unfold main4WilsonNeutralizerTotalMass
      simp
    _ = ∑ d ∈ P.divisors,
          lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
            ((M / d : ℕ) : ℝ) := by
      unfold main4WilsonReciprocalDivisorCoprimeSieveSum
      rw [show P.divisors.filter (fun d ↦ d.Coprime 1) = P.divisors by
        ext d
        simp]
      apply Finset.sum_congr rfl
      intro d hd
      have hfilter :
          (Finset.Icc 1 M).filter
              (fun m ↦ d ∣ m ∧ m.Coprime 1) =
            (Finset.Icc 1 M).filter (fun m ↦ d ∣ m) := by
        ext m
        simp
      rw [hfilter, card_Icc_filter_dvd_eq_div]

/-- The real main sum naturally paired with the neutralizer floor expansion. -/
def main4WilsonNeutralizerDivisorMainSum
    (P : ℕ) (lambdaPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ P.divisors,
    lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d /
      (d : ℝ)

/-- Replacing every `floor(M/d)` by `M/d` costs at most one absolute
coefficient per divisor. -/
theorem abs_main4WilsonNeutralizerTotalMass_sub_main_le_coefficientMass
    (P M : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ) :
    |main4WilsonNeutralizerTotalMass P M lambdaPlus -
        (M : ℝ) * main4WilsonNeutralizerDivisorMainSum P lambdaPlus| ≤
      main4WilsonNeutralizerCoefficientMass P lambdaPlus := by
  rw [main4WilsonNeutralizerTotalMass_eq_sum_natDiv P M hP lambdaPlus]
  unfold main4WilsonNeutralizerDivisorMainSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ P.divisors,
        (lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
            ((M / d : ℕ) : ℝ) -
          (M : ℝ) *
            (lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ)))| ≤
        ∑ d ∈ P.divisors,
          |lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
              ((M / d : ℕ) : ℝ) -
            (M : ℝ) *
              (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.divisors,
          |lambdaPlus d| *
            main4WilsonReciprocalDivisorComplementWeight d := by
      apply Finset.sum_le_sum
      intro d hdP
      have hd : 0 < d := Nat.pos_of_mem_divisors hdP
      have herr := abs_natCast_div_sub_div_le_one M d hd
      have hcomp :=
        main4WilsonReciprocalDivisorComplementWeight_nonneg d
      calc
        |lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
              ((M / d : ℕ) : ℝ) -
            (M : ℝ) *
              (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ))| =
            |lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d| *
              |((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)| := by
          rw [show
            lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
                  ((M / d : ℕ) : ℝ) -
                (M : ℝ) *
                  (lambdaPlus d *
                    main4WilsonReciprocalDivisorComplementWeight d /
                      (d : ℝ)) =
              (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
                (((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)) by ring,
            abs_mul]
        _ ≤ |lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d| * 1 := by
          exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
        _ = |lambdaPlus d| *
              main4WilsonReciprocalDivisorComplementWeight d := by
          rw [abs_mul, abs_of_nonneg hcomp, mul_one]
    _ = main4WilsonNeutralizerCoefficientMass P lambdaPlus := by
      rfl

/-- One-sided form used in the Selberg mass estimate. -/
theorem main4WilsonNeutralizerTotalMass_le_main_add_coefficientMass
    (P M : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ) :
    main4WilsonNeutralizerTotalMass P M lambdaPlus ≤
      (M : ℝ) * main4WilsonNeutralizerDivisorMainSum P lambdaPlus +
        main4WilsonNeutralizerCoefficientMass P lambdaPlus := by
  have h :=
    abs_main4WilsonNeutralizerTotalMass_sub_main_le_coefficientMass
      P M hP lambdaPlus
  linarith [le_abs_self
    (main4WilsonNeutralizerTotalMass P M lambdaPlus -
      (M : ℝ) * main4WilsonNeutralizerDivisorMainSum P lambdaPlus)]

end

end PellPaper
