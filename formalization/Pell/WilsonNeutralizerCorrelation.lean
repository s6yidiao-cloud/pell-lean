import Pell.WilsonNeutralizerMajorantReduction
import Pell.JacobiDenominatorPrefixCancellation

/-!
# Correlations of Wilson's finite neutralizer

This module performs the exact finite rearrangement used for the nonsquare
part of Wilson's Section 2 proof.  A correlation of the Hooley-neutralizer
majorant is written as a sum over sieve divisors followed by Jacobi prefixes.
For the source-faithful odd-supported majorant, the denominator-oriented
character modulo `4*q` from `JacobiDenominatorPrefixCancellation` supplies
the required Pólya--Vinogradov estimate.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

private theorem sum_multiples_jacobiSym
    (q d M : ℕ) (hd : 0 < d) :
    (∑ m ∈ (Finset.Icc 1 M).filter (fun m ↦ d ∣ m),
        (jacobiSym (q : ℤ) m : ℝ)) =
      ∑ k ∈ Finset.Icc 1 (M / d),
        (jacobiSym (q : ℤ) (d * k) : ℝ) := by
  classical
  refine Finset.sum_bij'
    (fun m _ ↦ m / d) (fun k _ ↦ d * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hmPos : 0 < m := zero_lt_one.trans_le hm.1.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hmPos hm.2) hd,
        Nat.div_le_div_right hm.1.2⟩
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hk.1,
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hd).mp hk.2⟩,
        Nat.dvd_mul_right d k⟩
  · intro m hm
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2
  · intro k hk
    exact Nat.mul_div_cancel_left k hd
  · intro m hm
    congr 1
    exact congrArg (fun t : ℕ ↦ jacobiSym (q : ℤ) t)
      (Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2).symm

private theorem sum_odd_multiples_jacobiSym
    (q d M : ℕ) (hd : 0 < d) (hdOdd : Odd d) :
    (∑ m ∈ (Finset.Icc 1 M).filter (fun m ↦ d ∣ m ∧ Odd m),
        (jacobiSym (q : ℤ) m : ℝ)) =
      ∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
        (jacobiSym (q : ℤ) (d * k) : ℝ) := by
  classical
  refine Finset.sum_bij'
    (fun m _ ↦ m / d) (fun k _ ↦ d * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hmPos : 0 < m := zero_lt_one.trans_le hm.1.1
    have hfactor : d * (m / d) = m := Nat.mul_div_cancel' hm.2.1
    have hkOdd : Odd (m / d) := by
      rw [← hfactor] at hm
      exact (Nat.odd_mul.mp hm.2.2).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.div_pos (Nat.le_of_dvd hmPos hm.2.1) hd,
          Nat.div_le_div_right hm.1.2⟩,
        hkOdd⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hk.1.1,
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hd).mp hk.1.2⟩,
        ⟨Nat.dvd_mul_right d k, hdOdd.mul hk.2⟩⟩
  · intro m hm
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2.1
  · intro k hk
    exact Nat.mul_div_cancel_left k hd
  · intro m hm
    congr 1
    exact congrArg (fun t : ℕ ↦ jacobiSym (q : ℤ) t)
      (Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2.1).symm

private theorem divisors_filter_comm
    {m P : ℕ} (hm : m ≠ 0) (hP : P ≠ 0) :
    m.divisors.filter (fun d ↦ d ∣ P) =
      P.divisors.filter (fun d ↦ d ∣ m) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdm, _hm⟩, hdP⟩
    exact ⟨⟨hdP, hP⟩, hdm⟩
  · rintro ⟨⟨hdP, _hP⟩, hdm⟩
    exact ⟨⟨hdm, hm⟩, hdP⟩

/-- Exact divisor-first expansion of a neutralizer correlation. -/
theorem wilsonJacobiCorrelation_neutralizer_eq_divisor_prefix_sum
    (P M q : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ) :
    wilsonJacobiCorrelation
        (main4WilsonNeutralizerMajorant P lambdaPlus) M q =
      ∑ d ∈ P.divisors,
        (lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) d : ℝ) *
          (∑ k ∈ Finset.Icc 1 (M / d),
            (jacobiSym (q : ℤ) k : ℝ)) := by
  classical
  unfold wilsonJacobiCorrelation main4WilsonNeutralizerMajorant
  calc
    (∑ m ∈ Finset.Icc 1 M,
        (∑ d ∈ m.divisors.filter (fun d ↦ d ∣ P),
            lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) m : ℝ)) =
        ∑ m ∈ Finset.Icc 1 M,
          ∑ d ∈ P.divisors,
            if d ∣ m then
              (lambdaPlus d *
                  main4WilsonReciprocalDivisorComplementWeight d) *
                (jacobiSym (q : ℤ) m : ℝ)
            else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hm).1
      rw [divisors_filter_comm hm0 hP, Finset.sum_filter]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdm : d ∣ m <;> simp [hdm]
    _ = ∑ d ∈ P.divisors,
          ∑ m ∈ Finset.Icc 1 M,
            if d ∣ m then
              (lambdaPlus d *
                  main4WilsonReciprocalDivisorComplementWeight d) *
                (jacobiSym (q : ℤ) m : ℝ)
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.divisors,
        (lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) d : ℝ) *
          (∑ k ∈ Finset.Icc 1 (M / d),
            (jacobiSym (q : ℤ) k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hdP
      have hd : 0 < d := Nat.pos_of_mem_divisors hdP
      calc
        (∑ m ∈ Finset.Icc 1 M,
            if d ∣ m then
              (lambdaPlus d *
                  main4WilsonReciprocalDivisorComplementWeight d) *
                (jacobiSym (q : ℤ) m : ℝ)
            else 0) =
            (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
              ∑ m ∈ (Finset.Icc 1 M).filter (fun m ↦ d ∣ m),
                (jacobiSym (q : ℤ) m : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_filter]
        _ = (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
              ∑ k ∈ Finset.Icc 1 (M / d),
                (jacobiSym (q : ℤ) (d * k) : ℝ) := by
          rw [sum_multiples_jacobiSym q d M hd]
        _ = (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
              (jacobiSym (q : ℤ) d : ℝ) *
              (∑ k ∈ Finset.Icc 1 (M / d),
                (jacobiSym (q : ℤ) k : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : k ≠ 0 :=
            Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
          rw [jacobiSym.mul_right' _ (Nat.ne_of_gt hd) hk0, Int.cast_mul]
          ring

/-- Divisor-first expansion with the odd support retained.  Because every
divisor of the odd sieve product is odd, the change of variables `m=d*k`
transports the odd restriction exactly to `k`. -/
theorem wilsonJacobiCorrelation_oddNeutralizer_eq_divisor_prefix_sum
    (P M q : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ) :
    wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M q =
      ∑ d ∈ P.divisors,
        (lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) d : ℝ) *
          (∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
            (jacobiSym (q : ℤ) k : ℝ)) := by
  classical
  unfold wilsonJacobiCorrelation main4WilsonOddNeutralizerMajorant
  calc
    (∑ m ∈ Finset.Icc 1 M,
        (if Odd m then main4WilsonNeutralizerMajorant P lambdaPlus m else 0) *
          (jacobiSym (q : ℤ) m : ℝ)) =
        ∑ m ∈ (Finset.Icc 1 M).filter Odd,
          main4WilsonNeutralizerMajorant P lambdaPlus m *
            (jacobiSym (q : ℤ) m : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hodd : Odd m <;> simp [hodd]
    _ = ∑ m ∈ (Finset.Icc 1 M).filter Odd,
          ∑ d ∈ P.divisors,
            if d ∣ m then
              (lambdaPlus d *
                  main4WilsonReciprocalDivisorComplementWeight d) *
                (jacobiSym (q : ℤ) m : ℝ)
            else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 :=
        Nat.ne_of_gt (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      unfold main4WilsonNeutralizerMajorant
      rw [divisors_filter_comm hm0 hP, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdm : d ∣ m <;> simp [hdm]
    _ = ∑ d ∈ P.divisors,
          ∑ m ∈ (Finset.Icc 1 M).filter Odd,
            if d ∣ m then
              (lambdaPlus d *
                  main4WilsonReciprocalDivisorComplementWeight d) *
                (jacobiSym (q : ℤ) m : ℝ)
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.divisors,
        (lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) d : ℝ) *
          (∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
            (jacobiSym (q : ℤ) k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hdP
      have hd : 0 < d := Nat.pos_of_mem_divisors hdP
      have hdOdd : Odd d := by
        obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors hdP
        rw [hc] at hPodd
        exact (Nat.odd_mul.mp hPodd).1
      calc
        (∑ m ∈ (Finset.Icc 1 M).filter Odd,
            if d ∣ m then
              (lambdaPlus d *
                  main4WilsonReciprocalDivisorComplementWeight d) *
                (jacobiSym (q : ℤ) m : ℝ)
            else 0) =
            (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
              ∑ m ∈ (Finset.Icc 1 M).filter
                (fun m ↦ d ∣ m ∧ Odd m),
                (jacobiSym (q : ℤ) m : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro m hm
          by_cases hodd : Odd m <;>
            by_cases hdm : d ∣ m <;> simp [hodd, hdm, and_comm]
        _ = (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
              ∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
                (jacobiSym (q : ℤ) (d * k) : ℝ) := by
          rw [sum_odd_multiples_jacobiSym q d M hd hdOdd]
        _ = (lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d) *
              (jacobiSym (q : ℤ) d : ℝ) *
              (∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
                (jacobiSym (q : ℤ) k : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : k ≠ 0 := Nat.ne_of_gt
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
          rw [jacobiSym.mul_right' _ (Nat.ne_of_gt hd) hk0, Int.cast_mul]
          ring

/-- For the reciprocal-divisor specialization, every complementary local
factor is `1/2`; the value therefore depends only on the number of distinct
prime factors. -/
theorem main4WilsonReciprocalDivisorComplementWeight_eq_half_pow (d : ℕ) :
    main4WilsonReciprocalDivisorComplementWeight d =
      (1 / 2 : ℝ) ^ d.primeFactors.card := by
  unfold main4WilsonReciprocalDivisorComplementWeight
  calc
    (∏ p ∈ d.primeFactors,
        (1 - main4WilsonReciprocalDivisorWeight p)) =
        ∏ _p ∈ d.primeFactors, (1 / 2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [main4WilsonReciprocalDivisorWeight_prime
        (Nat.prime_of_mem_primeFactors hp)]
      norm_num
    _ = (1 / 2 : ℝ) ^ d.primeFactors.card := by simp

theorem main4WilsonReciprocalDivisorComplementWeight_nonneg (d : ℕ) :
    0 ≤ main4WilsonReciprocalDivisorComplementWeight d := by
  rw [main4WilsonReciprocalDivisorComplementWeight_eq_half_pow]
  positivity

theorem abs_main4WilsonReciprocalDivisorComplementWeight_le_one (d : ℕ) :
    |main4WilsonReciprocalDivisorComplementWeight d| ≤ 1 := by
  rw [abs_of_nonneg
    (main4WilsonReciprocalDivisorComplementWeight_nonneg d),
    main4WilsonReciprocalDivisorComplementWeight_eq_half_pow]
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem abs_jacobiSym_real_le_one (q : ℤ) (d : ℕ) :
    |(jacobiSym q d : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy q d with h | h | h <;> rw [h] <;> norm_num

/-- A divisor-supported neutralizer correlation is bounded by the number of
possible supported divisors times any uniform bound for the ordinary Jacobi
prefixes.  This is the finite triangle-inequality step immediately before
Pólya--Vinogradov in Wilson's nonsquare argument. -/
theorem abs_wilsonJacobiCorrelation_neutralizer_le_of_prefix_bound
    (P M q y : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0)
    (hprefix : ∀ X : ℕ,
      |∑ k ∈ Finset.Icc 1 X, (jacobiSym (q : ℤ) k : ℝ)| ≤ B) :
    |wilsonJacobiCorrelation
        (main4WilsonNeutralizerMajorant P lambdaPlus) M q| ≤
      (y : ℝ) * B := by
  rw [wilsonJacobiCorrelation_neutralizer_eq_divisor_prefix_sum
    P M q hP lambdaPlus]
  have hcard :
      (((P.divisors.filter (fun d ↦ d ≤ y)).card : ℕ) : ℝ) ≤ (y : ℝ) := by
    have hcardNat :
        (P.divisors.filter (fun d ↦ d ≤ y)).card ≤
          (Finset.Icc 1 y).card :=
      Finset.card_le_card (show
        P.divisors.filter (fun d ↦ d ≤ y) ⊆ Finset.Icc 1 y by
          intro d hd
          obtain ⟨hdP, hdy⟩ := Finset.mem_filter.mp hd
          exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdy⟩)
    have hcardNat' :
        (P.divisors.filter (fun d ↦ d ≤ y)).card ≤ y := by
      simpa using hcardNat
    exact_mod_cast hcardNat'
  calc
    |∑ d ∈ P.divisors,
        (lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d) *
          (jacobiSym (q : ℤ) d : ℝ) *
          (∑ k ∈ Finset.Icc 1 (M / d),
            (jacobiSym (q : ℤ) k : ℝ))| ≤
        ∑ d ∈ P.divisors,
          |(lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d) *
            (jacobiSym (q : ℤ) d : ℝ) *
            (∑ k ∈ Finset.Icc 1 (M / d),
              (jacobiSym (q : ℤ) k : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.divisors, if d ≤ y then B else 0 := by
      apply Finset.sum_le_sum
      intro d hdP
      by_cases hdy : d ≤ y
      · rw [if_pos hdy]
        simp only [abs_mul]
        calc
          |lambdaPlus d| *
                |main4WilsonReciprocalDivisorComplementWeight d| *
              |(jacobiSym (q : ℤ) d : ℝ)| *
              |∑ k ∈ Finset.Icc 1 (M / d),
                (jacobiSym (q : ℤ) k : ℝ)| ≤
              1 * 1 * 1 * B := by
            gcongr
            · exact hlambda d hdP
            · exact abs_main4WilsonReciprocalDivisorComplementWeight_le_one d
            · exact abs_jacobiSym_real_le_one q d
            · exact hprefix (M / d)
          _ = B := by ring
      · rw [if_neg hdy]
        have hzero : lambdaPlus d = 0 :=
          hsupport d hdP (by omega)
        simp [hzero]
    _ = (((P.divisors.filter (fun d ↦ d ≤ y)).card : ℕ) : ℝ) * B := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (y : ℝ) * B := mul_le_mul_of_nonneg_right hcard hB

/-- Odd-supported counterpart of the preceding triangle-inequality lemma.
The retained odd filter is essential: it is exactly the domain on which the
denominator Jacobi symbol is represented by the genuine character modulo
`4*q`. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_le_of_prefix_bound
    (P M q y : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0)
    (hprefix : ∀ X : ℕ,
      |∑ k ∈ (Finset.Icc 1 X).filter Odd,
        (jacobiSym (q : ℤ) k : ℝ)| ≤ B) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M q| ≤
      (y : ℝ) * B := by
  rw [wilsonJacobiCorrelation_oddNeutralizer_eq_divisor_prefix_sum
    P M q hP hPodd lambdaPlus]
  have hcard :
      (((P.divisors.filter (fun d ↦ d ≤ y)).card : ℕ) : ℝ) ≤ (y : ℝ) := by
    have hcardNat :
        (P.divisors.filter (fun d ↦ d ≤ y)).card ≤
          (Finset.Icc 1 y).card :=
      Finset.card_le_card (show
        P.divisors.filter (fun d ↦ d ≤ y) ⊆ Finset.Icc 1 y by
          intro d hd
          obtain ⟨hdP, hdy⟩ := Finset.mem_filter.mp hd
          exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdy⟩)
    have hcardNat' :
        (P.divisors.filter (fun d ↦ d ≤ y)).card ≤ y := by
      simpa using hcardNat
    exact_mod_cast hcardNat'
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
    _ ≤ ∑ d ∈ P.divisors, if d ≤ y then B else 0 := by
      apply Finset.sum_le_sum
      intro d hdP
      by_cases hdy : d ≤ y
      · rw [if_pos hdy]
        simp only [abs_mul]
        calc
          |lambdaPlus d| *
                |main4WilsonReciprocalDivisorComplementWeight d| *
              |(jacobiSym (q : ℤ) d : ℝ)| *
              |∑ k ∈ (Finset.Icc 1 (M / d)).filter Odd,
                (jacobiSym (q : ℤ) k : ℝ)| ≤
              1 * 1 * 1 * B := by
            gcongr
            · exact hlambda d hdP
            · exact abs_main4WilsonReciprocalDivisorComplementWeight_le_one d
            · exact abs_jacobiSym_real_le_one q d
            · exact hprefix (M / d)
          _ = B := by ring
      · rw [if_neg hdy]
        have hzero : lambdaPlus d = 0 :=
          hsupport d hdP (by omega)
        simp [hzero]
    _ = (((P.divisors.filter (fun d ↦ d ≤ y)).card : ℕ) : ℝ) * B := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (y : ℝ) * B := mul_le_mul_of_nonneg_right hcard hB

/-- Wilson's denominator-side Pólya--Vinogradov step, now discharged rather
than assumed.  The modulus is `4*q`, which simultaneously handles the two
quadratic-reciprocity sign branches and vanishes on even denominators. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_le
    (P M q y : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ)
    (hq : 0 < q) (hqodd : Odd q) (hqsquare : ¬ IsSquare q)
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M q| ≤
      (y : ℝ) *
        (2 * Real.sqrt (4 * (q : ℝ)) *
          (1 + Real.log (4 * (q : ℝ)))) := by
  have hlog : 0 ≤ Real.log (4 * (q : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 4 * q by omega)
  apply abs_wilsonJacobiCorrelation_oddNeutralizer_le_of_prefix_bound
    P M q y hP hPodd lambdaPlus
      (2 * Real.sqrt (4 * (q : ℝ)) *
        (1 + Real.log (4 * (q : ℝ)))) (by positivity)
      hlambda hsupport
  intro X
  exact abs_sum_jacobiSym_denominator_odd_le q X hq hqodd hqsquare

/-- A numerator-box-uniform form of the preceding bound.  The deliberately
roomy logarithm keeps the proof monotone and avoids hiding constants in
asymptotic notation. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_mul_le
    (P M n₁ n₂ N y : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hn₁N : n₁ ≤ N) (hn₂N : n₂ ≤ N)
    (hodd : Odd (n₁ * n₂)) (hns : ¬ IsSquare (n₁ * n₂))
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n₁ * n₂)| ≤
      (y : ℝ) *
        (4 * (N : ℝ) *
          (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by
  have hN : 0 < N := hn₁.trans_le hn₁N
  have hqNat : n₁ * n₂ ≤ N * N := Nat.mul_le_mul hn₁N hn₂N
  have harg :
      4 * ((n₁ * n₂ : ℕ) : ℝ) ≤ (2 * (N : ℝ)) ^ 2 := by
    exact_mod_cast (show 4 * (n₁ * n₂) ≤ (2 * N) ^ 2 by
      nlinarith)
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
  have hlogRight :
      0 ≤ 1 + Real.log ((2 * (N : ℝ)) ^ 2) := by
    have : 0 ≤ Real.log ((2 * (N : ℝ)) ^ 2) := by
      apply Real.log_nonneg
      nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
    linarith
  have hc := abs_wilsonJacobiCorrelation_oddNeutralizer_le
    P M (n₁ * n₂) y hP hPodd lambdaPlus
      (Nat.mul_pos hn₁ hn₂) hodd hns hlambda hsupport
  calc
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n₁ * n₂)| ≤
        (y : ℝ) *
          (2 * Real.sqrt (4 * ((n₁ * n₂ : ℕ) : ℝ)) *
            (1 + Real.log (4 * ((n₁ * n₂ : ℕ) : ℝ)))) := hc
    _ ≤ (y : ℝ) *
          (2 * (2 * (N : ℝ)) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by
      gcongr
    _ = (y : ℝ) *
          (4 * (N : ℝ) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by ring

/-- The source-faithful nonsquare contribution in Wilson's expanded second
moment, with the denominator Pólya--Vinogradov premise completely discharged.
Its right side is explicitly of order `y * N^3 * log N`. -/
theorem abs_sum_nonsquare_wilsonOddNeutralizerCorrelation_le
    (a : ℕ → ℝ) (P M N y : ℕ) (hP : P ≠ 0) (hPodd : Odd P)
    (lambdaPlus : ℕ → ℝ)
    (ha : main4OddSupportedUnitBound a)
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0) :
    |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun p ↦ ¬ IsSquare (p.1 * p.2)),
      a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
          (p.1 * p.2)| ≤
      (N : ℝ) ^ 2 *
        ((y : ℝ) *
          (4 * (N : ℝ) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2)))) := by
  classical
  let S := ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p ↦ ¬ IsSquare (p.1 * p.2))
  let B := (y : ℝ) *
    (4 * (N : ℝ) * (1 + Real.log ((2 * (N : ℝ)) ^ 2)))
  have hB : 0 ≤ B := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp [B]
    · have hlog : 0 ≤ Real.log ((2 * (N : ℝ)) ^ 2) := by
        apply Real.log_nonneg
        have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hNpos]
      dsimp [B]
      positivity
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
          abs_wilsonJacobiCorrelation_oddNeutralizer_mul_le
            P M p.1 p.2 N y hP hPodd lambdaPlus
              hp₁pos hp₂pos hp₁N hp₂N (hp₁odd.mul hp₂odd) hns
              hlambda hsupport
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
              ((y : ℝ) *
                (4 * (N : ℝ) *
                  (1 + Real.log ((2 * (N : ℝ)) ^ 2)))) := by
            gcongr
            · exact ha.2 p.1
            · exact ha.2 p.2
          _ = (y : ℝ) *
                (4 * (N : ℝ) *
                  (1 + Real.log ((2 * (N : ℝ)) ^ 2))) := by ring
  have hcard : (S.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤
          ((((Finset.Icc 1 N).product (Finset.Icc 1 N)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (N : ℝ) ^ 2 := by simp [pow_two]
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
    _ ≤ ∑ _p ∈ S, B := Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ = (S.card : ℝ) * B := by simp
    _ ≤ (N : ℝ) ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB
    _ = (N : ℝ) ^ 2 *
        ((y : ℝ) *
          (4 * (N : ℝ) *
            (1 + Real.log ((2 * (N : ℝ)) ^ 2)))) := rfl

/-- Wilson's nonsquare correlation bound after supplying the denominator-side
Jacobi prefix estimate used in the paper.  This orientation is
`sum_k (q/k)`; it is intentionally not confused with the already proved
numerator-side theorem `sum_k (k/q)`. -/
theorem abs_wilsonJacobiCorrelation_neutralizer_mul_le_of_denominator_prefix
    (P M n₁ n₂ N y : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ)
    (hn₁ : 0 < n₁) (_hn₂ : 0 < n₂)
    (hn₁N : n₁ ≤ N) (_hn₂N : n₂ ≤ N)
    (_hodd : Odd (n₁ * n₂)) (_hns : ¬ IsSquare (n₁ * n₂))
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0)
    (hprefix : ∀ X : ℕ,
      |∑ k ∈ Finset.Icc 1 X,
        (jacobiSym ((n₁ * n₂ : ℕ) : ℤ) k : ℝ)| ≤
          2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))) :
    |wilsonJacobiCorrelation
        (main4WilsonNeutralizerMajorant P lambdaPlus) M (n₁ * n₂)| ≤
      (y : ℝ) *
        (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))) := by
  have hN : 0 < N := hn₁.trans_le hn₁N
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  apply abs_wilsonJacobiCorrelation_neutralizer_le_of_prefix_bound
    P M (n₁ * n₂) y hP lambdaPlus
      (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))) (by positivity)
      hlambda hsupport
  exact hprefix

/-- Summing the preceding pointwise estimate over the nonsquare part of the
`N × N` numerator box gives Wilson's `y N^3 log N` contribution.  Even
numerators vanish by the source coefficient hypothesis. -/
theorem abs_sum_nonsquare_wilsonNeutralizerCorrelation_le
    (a : ℕ → ℝ) (P M N y : ℕ) (hP : P ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (ha : main4OddSupportedUnitBound a)
    (hlambda : ∀ d ∈ P.divisors, |lambdaPlus d| ≤ 1)
    (hsupport : ∀ d ∈ P.divisors, y < d → lambdaPlus d = 0)
    (hprefix : ∀ (n₁ n₂ : ℕ), 0 < n₁ → 0 < n₂ →
      n₁ ≤ N → n₂ ≤ N → Odd (n₁ * n₂) → ¬ IsSquare (n₁ * n₂) →
      ∀ X : ℕ,
        |∑ k ∈ Finset.Icc 1 X,
          (jacobiSym ((n₁ * n₂ : ℕ) : ℤ) k : ℝ)| ≤
            2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))) :
    |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun p ↦ ¬ IsSquare (p.1 * p.2)),
      a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonNeutralizerMajorant P lambdaPlus) M
          (p.1 * p.2)| ≤
      (N : ℝ) ^ 2 *
        ((y : ℝ) *
          (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)))) := by
  classical
  let S := ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p ↦ ¬ IsSquare (p.1 * p.2))
  let B := (y : ℝ) *
    (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)))
  have hB : 0 ≤ B := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp [B]
    · have hlog : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hN)
      dsimp [B]
      positivity
  have hpoint (p : ℕ × ℕ) (hp : p ∈ S) :
      |a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonNeutralizerMajorant P lambdaPlus) M
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
          abs_wilsonJacobiCorrelation_neutralizer_mul_le_of_denominator_prefix
          P M p.1 p.2 N y hP lambdaPlus hp₁pos hp₂pos hp₁N hp₂N
            (hp₁odd.mul hp₂odd) hns hlambda hsupport
              (hprefix p.1 p.2 hp₁pos hp₂pos hp₁N hp₂N
                (hp₁odd.mul hp₂odd) hns)
        dsimp [B]
        calc
          |a p.1 * a p.2 *
              wilsonJacobiCorrelation
                (main4WilsonNeutralizerMajorant P lambdaPlus) M
                (p.1 * p.2)| =
              |a p.1| * |a p.2| *
                |wilsonJacobiCorrelation
                  (main4WilsonNeutralizerMajorant P lambdaPlus) M
                  (p.1 * p.2)| := by simp only [abs_mul]
          _ ≤ 1 * 1 *
              ((y : ℝ) *
                (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)))) := by
            gcongr
            · exact ha.2 p.1
            · exact ha.2 p.2
          _ = (y : ℝ) *
                (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))) := by ring
  have hcard : (S.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤
          ((((Finset.Icc 1 N).product (Finset.Icc 1 N)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (N : ℝ) ^ 2 := by simp [pow_two]
  calc
    |∑ p ∈ S,
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤
        ∑ p ∈ S,
          |a p.1 * a p.2 *
            wilsonJacobiCorrelation
              (main4WilsonNeutralizerMajorant P lambdaPlus) M
              (p.1 * p.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, B := Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ = (S.card : ℝ) * B := by simp
    _ ≤ (N : ℝ) ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB
    _ = (N : ℝ) ^ 2 *
        ((y : ℝ) *
          (2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)))) := rfl

end

end PellPaper
