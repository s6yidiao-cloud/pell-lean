import Pell.WilsonSelbergShortUpperWeights
import Pell.WilsonNeutralizerCorrelationCoefficientMass

/-!
# Polynomial coefficient mass for short Selberg upper weights

The Lambda-squared Selberg coefficients satisfy `|muPlus(d)| <= d^2` and
vanish above their level.  This gives a deliberately coarse `y^3` bound for
the absolute coefficient mass.  A smaller power choice for `y` absorbs this
loss into Wilson's flexible `M^epsilon` term.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

theorem main4WilsonNeutralizerCoefficientMass_selberg_le_cube
    (s : SelbergSieve) (y : ℕ) (hy : s.level = (y : ℝ)) :
    main4WilsonNeutralizerCoefficientMass
        s.toBoundingSieve.prodPrimes (main4SelbergMuPlus s) ≤
      (y : ℝ) ^ 3 := by
  let P := s.toBoundingSieve.prodPrimes
  let muPlus := main4SelbergMuPlus s
  have hcard :
      (((P.divisors.filter (fun d ↦ d ≤ y)).card : ℕ) : ℝ) ≤ (y : ℝ) := by
    have hcardNat :
        (P.divisors.filter (fun d ↦ d ≤ y)).card ≤
          (Finset.Icc 1 y).card :=
      Finset.card_le_card (show
        P.divisors.filter (fun d ↦ d ≤ y) ⊆ Finset.Icc 1 y by
          intro d hd
          obtain ⟨hdP, hdy⟩ := Finset.mem_filter.mp hd
          exact Finset.mem_Icc.mpr
            ⟨Nat.pos_of_mem_divisors hdP, hdy⟩)
    exact_mod_cast (show
      (P.divisors.filter (fun d ↦ d ≤ y)).card ≤ y by
        simpa using hcardNat)
  unfold main4WilsonNeutralizerCoefficientMass
  change
    (∑ d ∈ P.divisors,
      |muPlus d| * main4WilsonReciprocalDivisorComplementWeight d) ≤ _
  calc
    (∑ d ∈ P.divisors,
        |muPlus d| * main4WilsonReciprocalDivisorComplementWeight d) ≤
        ∑ d ∈ P.divisors, if d ≤ y then (y : ℝ) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro d hdP
      by_cases hdy : d ≤ y
      · rw [if_pos hdy]
        have hmu : |muPlus d| ≤ (d : ℝ) ^ 2 :=
          main4SelbergMuPlus_abs_le_sq s d hdP
        have hcomp :
            main4WilsonReciprocalDivisorComplementWeight d ≤ 1 := by
          rw [← abs_of_nonneg
            (main4WilsonReciprocalDivisorComplementWeight_nonneg d)]
          exact abs_main4WilsonReciprocalDivisorComplementWeight_le_one d
        calc
          |muPlus d| * main4WilsonReciprocalDivisorComplementWeight d ≤
              (d : ℝ) ^ 2 * 1 := by
            exact mul_le_mul hmu hcomp
              (main4WilsonReciprocalDivisorComplementWeight_nonneg d)
              (by positivity)
          _ ≤ (y : ℝ) ^ 2 := by
            simpa only [mul_one] using
              (show (d : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 by
                exact_mod_cast Nat.pow_le_pow_left hdy 2)
      · rw [if_neg hdy]
        have hnot : ¬(d : ℝ) ≤ s.level := by
          rw [hy]
          exact_mod_cast hdy
        change |main4SelbergMuPlus s d| *
            main4WilsonReciprocalDivisorComplementWeight d ≤ 0
        rw [main4SelbergMuPlus_eq_zero s d hnot, abs_zero, zero_mul]
    _ = (((P.divisors.filter (fun d ↦ d ≤ y)).card : ℕ) : ℝ) *
          (y : ℝ) ^ 2 := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (y : ℝ) * (y : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg (y : ℝ))
    _ = (y : ℝ) ^ 3 := by ring

end

end PellPaper
