import Mathlib.NumberTheory.Primorial
import Pell.WilsonNeutralizerCorrelationCoefficientMass

/-!
# Removing the prime two from Wilson's primorial neutralizer

Mathlib's Selberg construction naturally uses the full primorial, whereas
Wilson's denominator-character argument is most naturally indexed by the
product of the odd sieve primes.  This file proves that deleting the single
factor `2` does not change the neutralizer on odd denominators, and can only
decrease its absolute coefficient mass.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The product of the odd primes at most `z`, represented as the full
primorial with its factor `2` removed.  The hypotheses `2 ≤ z` on the
lemmas below ensure that the division is exact. -/
def main4WilsonOddPrimorial (z : ℕ) : ℕ :=
  primorial z / 2

private theorem two_dvd_primorial {z : ℕ} (hz : 2 ≤ z) :
    2 ∣ primorial z := by
  exact Nat.prime_two.dvd_primorial_iff.mpr hz

/-- For `z ≥ 2`, the full primorial is twice its odd part. -/
theorem primorial_eq_two_mul_main4WilsonOddPrimorial
    {z : ℕ} (hz : 2 ≤ z) :
    primorial z = 2 * main4WilsonOddPrimorial z := by
  unfold main4WilsonOddPrimorial
  exact (Nat.mul_div_cancel' (two_dvd_primorial hz)).symm

/-- Removing the factor `2` from a primorial preserves squarefreeness. -/
theorem main4WilsonOddPrimorial_squarefree
    {z : ℕ} (hz : 2 ≤ z) :
    Squarefree (main4WilsonOddPrimorial z) := by
  apply (squarefree_primorial z).squarefree_of_dvd
  unfold main4WilsonOddPrimorial
  exact Nat.div_dvd_of_dvd (two_dvd_primorial hz)

/-- The primorial with its unique factor `2` removed is odd. -/
theorem main4WilsonOddPrimorial_odd
    {z : ℕ} (hz : 2 ≤ z) :
    Odd (main4WilsonOddPrimorial z) := by
  have hsq : Squarefree (2 * main4WilsonOddPrimorial z) := by
    rw [← primorial_eq_two_mul_main4WilsonOddPrimorial hz]
    exact squarefree_primorial z
  exact (Nat.coprime_of_squarefree_mul hsq).odd_of_left

theorem main4WilsonOddPrimorial_ne_zero
    {z : ℕ} (hz : 2 ≤ z) :
    main4WilsonOddPrimorial z ≠ 0 := by
  rcases main4WilsonOddPrimorial_odd hz with ⟨k, hk⟩
  intro hzero
  rw [hzero] at hk
  omega

private theorem dvd_primorial_iff_dvd_oddPrimorial_of_dvd_odd
    {z m d : ℕ} (hz : 2 ≤ z) (hm : Odd m) (hdm : d ∣ m) :
    d ∣ primorial z ↔ d ∣ main4WilsonOddPrimorial z := by
  have hdOdd : Odd d := by
    apply Nat.not_even_iff_odd.mp
    intro hdEven
    exact (Nat.not_even_iff_odd.mpr hm) (hdEven.trans_dvd hdm)
  rw [primorial_eq_two_mul_main4WilsonOddPrimorial hz]
  exact hdOdd.coprime_two_right.dvd_mul_left

/-- On an odd denominator, the neutralizer built from the full primorial is
exactly the neutralizer built from the odd primorial, with unchanged
coefficients. -/
theorem main4WilsonNeutralizerMajorant_primorial_eq_oddPrimorial_of_odd
    (z m : ℕ) (hz : 2 ≤ z) (hm : Odd m)
    (lambdaPlus : ℕ → ℝ) :
    main4WilsonNeutralizerMajorant (primorial z) lambdaPlus m =
      main4WilsonNeutralizerMajorant
        (main4WilsonOddPrimorial z) lambdaPlus m := by
  unfold main4WilsonNeutralizerMajorant
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hdm, hdP⟩
    exact ⟨hdm,
      (dvd_primorial_iff_dvd_oddPrimorial_of_dvd_odd hz hm
        (Nat.dvd_of_mem_divisors hdm)).mp hdP⟩
  · rintro ⟨hdm, hdQ⟩
    exact ⟨hdm,
      (dvd_primorial_iff_dvd_oddPrimorial_of_dvd_odd hz hm
        (Nat.dvd_of_mem_divisors hdm)).mpr hdQ⟩

/-- The odd-supported neutralizer functions for the full and odd primorials
are pointwise equal. -/
theorem main4WilsonOddNeutralizerMajorant_primorial_eq_oddPrimorial
    (z m : ℕ) (hz : 2 ≤ z) (lambdaPlus : ℕ → ℝ) :
    main4WilsonOddNeutralizerMajorant (primorial z) lambdaPlus m =
      main4WilsonOddNeutralizerMajorant
        (main4WilsonOddPrimorial z) lambdaPlus m := by
  unfold main4WilsonOddNeutralizerMajorant
  by_cases hm : Odd m
  · rw [if_pos hm, if_pos hm]
    exact
      main4WilsonNeutralizerMajorant_primorial_eq_oddPrimorial_of_odd
        z m hz hm lambdaPlus
  · rw [if_neg hm, if_neg hm]

/-- Function-level form of the pointwise odd-neutralizer identity. -/
theorem main4WilsonOddNeutralizerMajorant_primorial_fun_eq
    (z : ℕ) (hz : 2 ≤ z) (lambdaPlus : ℕ → ℝ) :
    main4WilsonOddNeutralizerMajorant (primorial z) lambdaPlus =
      main4WilsonOddNeutralizerMajorant
        (main4WilsonOddPrimorial z) lambdaPlus := by
  funext m
  exact main4WilsonOddNeutralizerMajorant_primorial_eq_oddPrimorial
    z m hz lambdaPlus

/-- Removing the factor `2` does not change any correlation of Wilson's
odd-supported neutralizer. -/
theorem wilsonJacobiCorrelation_primorialOddNeutralizer_eq
    (z M q : ℕ) (hz : 2 ≤ z) (lambdaPlus : ℕ → ℝ) :
    wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant
          (primorial z) lambdaPlus) M q =
      wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant
          (main4WilsonOddPrimorial z) lambdaPlus) M q := by
  rw [main4WilsonOddNeutralizerMajorant_primorial_fun_eq
    z hz lambdaPlus]

/-- Passing from the full primorial to its odd part can only remove
nonnegative summands from the absolute neutralizer coefficient mass. -/
theorem main4WilsonNeutralizerCoefficientMass_oddPrimorial_le_primorial
    (z : ℕ) (hz : 2 ≤ z) (lambdaPlus : ℕ → ℝ) :
    main4WilsonNeutralizerCoefficientMass
        (main4WilsonOddPrimorial z) lambdaPlus ≤
      main4WilsonNeutralizerCoefficientMass
        (primorial z) lambdaPlus := by
  unfold main4WilsonNeutralizerCoefficientMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Nat.divisors_subset_of_dvd (primorial_ne_zero z)
    unfold main4WilsonOddPrimorial
    exact Nat.div_dvd_of_dvd (two_dvd_primorial hz)
  · intro d _hdP _hdQ
    exact mul_nonneg (abs_nonneg _)
      (main4WilsonReciprocalDivisorComplementWeight_nonneg d)

end

end PellPaper
