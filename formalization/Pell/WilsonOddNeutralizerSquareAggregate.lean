import Pell.WilsonNeutralizerMajorantReduction
import Pell.WilsonReciprocalDivisorEulerFactor

/-!
# Wilson's square neutralizer aggregate from the coprime upper sieve

This module isolates the one analytic input used on the square diagonal in
Wilson's Section 2 argument.  At the reciprocal-divisor weight, the input is
the specialization of Wilson's Lemma 2.2 to the complementary function
`fHat(p) = 1/2`.  Everything after that input is finite: a square Jacobi
symbol is a coprimality indicator, square products are grouped by their
positive square root, and the Euler-factor and divisor-sum bounds already
proved in this project finish the aggregate.

The analytic input remains an explicit hypothesis.  In particular, this
file does not construct Brun's upper coefficients or prove the fundamental
lemma of sieve theory.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The exact finite coprime sum on the left of Wilson's Lemma 2.2 after
specializing its sieve weight to the reciprocal-divisor complementary
weight.  The restriction `d ≤ M` from the printed statement is redundant:
if `d > M`, the inner set of multiples is empty. -/
def main4WilsonReciprocalDivisorCoprimeSieveSum
    (P M n : ℕ) (lambdaPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ P.divisors.filter (fun d ↦ d.Coprime n),
    lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d *
      (((Finset.Icc 1 M).filter
        (fun m ↦ d ∣ m ∧ m.Coprime n)).card : ℝ)

/-- The right side of Wilson's Lemma 2.2 for `fHat(p)=1/2`, with an explicit
support parameter `y`.  The first summand is its main sieve term and the
second is the elementary endpoint error. -/
def main4WilsonReciprocalDivisorCoprimeSieveScale
    (P M y n : ℕ) : ℝ :=
  (M : ℝ) / Real.sqrt (Real.log (M : ℝ)) *
      ((n.totient : ℝ) / (n : ℝ) *
        main4WilsonReciprocalDivisorSieveFactor P n) +
    (y : ℝ) * (n.divisors.card : ℝ)

/-- The sole analytic interface in this module: Wilson's Lemma 2.2 at the
reciprocal-divisor complementary weight.  The constant is uniform in the
coprimality parameter `n`, exactly as required on the square diagonal. -/
def Main4WilsonReciprocalDivisorCoprimeUpperSieveWith
    (P M y : ℕ) (lambdaPlus : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    |main4WilsonReciprocalDivisorCoprimeSieveSum P M n lambdaPlus| ≤
      C * main4WilsonReciprocalDivisorCoprimeSieveScale P M y n

private theorem jacobiSym_nat_sq_cast_eq_coprimeIndicator
    (n m : ℕ) (hm : m ≠ 0) :
    (jacobiSym (((n ^ 2 : ℕ) : ℤ)) m : ℝ) =
      if n.Coprime m then 1 else 0 := by
  by_cases hcop : n.Coprime m
  · rw [if_pos hcop]
    have hgcd : (n : ℤ).gcd (m : ℤ) = 1 := by
      simpa [Int.gcd_eq_natAbs] using hcop.gcd_eq_one
    have hj : jacobiSym (((n ^ 2 : ℕ) : ℤ)) m = 1 := by
      simpa [Int.natCast_pow] using jacobiSym.sq_one' hgcd
    exact_mod_cast hj
  · rw [if_neg hcop]
    let _ : NeZero m := ⟨hm⟩
    have hpow : ¬ (n ^ 2).Coprime m := by
      simpa only [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)] using hcop
    have hgcd : (((n ^ 2 : ℕ) : ℤ)).gcd (m : ℤ) ≠ 1 := by
      simpa [Int.gcd_eq_natAbs, Nat.coprime_iff_gcd_eq_one] using hpow
    have hj : jacobiSym (((n ^ 2 : ℕ) : ℤ)) m = 0 :=
      jacobiSym.eq_zero_iff_not_coprime.mpr hgcd
    exact_mod_cast hj

private theorem main4WilsonNeutralizerMajorant_nonneg
    (P m : ℕ) (hP : Squarefree P) (hm : m ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    0 ≤ main4WilsonNeutralizerMajorant P lambdaPlus m := by
  exact (main4WilsonReciprocalDivisorWeight_nonneg m).trans
    (main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
      P m hP hm lambdaPlus hUpper)

private theorem main4WilsonOddNeutralizerMajorant_nonneg
    (P m : ℕ) (hP : Squarefree P) (hm : m ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    0 ≤ main4WilsonOddNeutralizerMajorant P lambdaPlus m := by
  unfold main4WilsonOddNeutralizerMajorant
  by_cases hodd : Odd m
  · rw [if_pos hodd]
    exact main4WilsonNeutralizerMajorant_nonneg
      P m hP hm lambdaPlus hUpper
  · simp [hodd]

private theorem divisors_filter_comm_for_square_sieve
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

/-- Expanding the neutralizer against a coprimality indicator gives exactly
the coprime upper-sieve sum. -/
theorem sum_main4WilsonNeutralizerMajorant_coprimeIndicator_eq_sieveSum
    (P M n : ℕ) (hP : P ≠ 0) (lambdaPlus : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 M,
        main4WilsonNeutralizerMajorant P lambdaPlus m *
          (if m.Coprime n then (1 : ℝ) else 0)) =
      main4WilsonReciprocalDivisorCoprimeSieveSum P M n lambdaPlus := by
  classical
  unfold main4WilsonReciprocalDivisorCoprimeSieveSum
  calc
    (∑ m ∈ Finset.Icc 1 M,
        main4WilsonNeutralizerMajorant P lambdaPlus m *
          (if m.Coprime n then (1 : ℝ) else 0)) =
        ∑ m ∈ Finset.Icc 1 M,
          ∑ d ∈ P.divisors,
            if d ∣ m ∧ m.Coprime n then
              lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d
            else 0 := by
      apply Finset.sum_congr rfl
      intro m hmMem
      have hm : m ≠ 0 :=
        Nat.ne_of_gt (Finset.mem_Icc.mp hmMem).1
      unfold main4WilsonNeutralizerMajorant
      rw [divisors_filter_comm_for_square_sieve hm hP,
        Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdm : d ∣ m <;>
        by_cases hcop : m.Coprime n <;> simp [hdm, hcop]
    _ = ∑ d ∈ P.divisors,
          ∑ m ∈ Finset.Icc 1 M,
            if d ∣ m ∧ m.Coprime n then
              lambdaPlus d *
                main4WilsonReciprocalDivisorComplementWeight d
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.divisors,
          lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d *
            (((Finset.Icc 1 M).filter
              (fun m ↦ d ∣ m ∧ m.Coprime n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp
      ring
    _ = ∑ d ∈ P.divisors.filter (fun d ↦ d.Coprime n),
          lambdaPlus d *
              main4WilsonReciprocalDivisorComplementWeight d *
            (((Finset.Icc 1 M).filter
              (fun m ↦ d ∣ m ∧ m.Coprime n)).card : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hdP
      by_cases hdCop : d.Coprime n
      · simp [hdCop]
      · have hempty :
            (Finset.Icc 1 M).filter
                (fun m ↦ d ∣ m ∧ m.Coprime n) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro m hmBox hpred
          obtain ⟨hdm, hmCop⟩ := hpred
          exact hdCop (Nat.Coprime.of_dvd_left hdm hmCop)
        simp [hdCop, hempty]

/-- On a square numerator, the odd neutralizer correlation is nonnegative:
the Jacobi symbol is precisely the coprimality indicator. -/
theorem wilsonJacobiCorrelation_oddNeutralizer_sq_nonneg
    (P M n : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    0 ≤ wilsonJacobiCorrelation
      (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n ^ 2) := by
  unfold wilsonJacobiCorrelation
  apply Finset.sum_nonneg
  intro m hmMem
  have hm : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hmMem).1
  rw [jacobiSym_nat_sq_cast_eq_coprimeIndicator n m hm]
  by_cases hcop : n.Coprime m
  · rw [if_pos hcop, mul_one]
    exact main4WilsonOddNeutralizerMajorant_nonneg
      P m hP hm lambdaPlus hUpper
  · simp [hcop]

/-- The source-shaped odd correlation at a square is bounded by the absolute
value of Wilson's full coprime upper-sieve sum.  Dropping the odd restriction
is legitimate only here, after using positivity of the neutralizer. -/
theorem wilsonJacobiCorrelation_oddNeutralizer_sq_le_abs_sieveSum
    (P M n : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n ^ 2) ≤
      |main4WilsonReciprocalDivisorCoprimeSieveSum P M n lambdaPlus| := by
  calc
    wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n ^ 2) =
        ∑ m ∈ Finset.Icc 1 M,
          main4WilsonOddNeutralizerMajorant P lambdaPlus m *
            (if m.Coprime n then (1 : ℝ) else 0) := by
      unfold wilsonJacobiCorrelation
      apply Finset.sum_congr rfl
      intro m hmMem
      have hm : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hmMem).1
      rw [jacobiSym_nat_sq_cast_eq_coprimeIndicator n m hm]
      simp only [Nat.coprime_comm]
    _ ≤ ∑ m ∈ Finset.Icc 1 M,
          main4WilsonNeutralizerMajorant P lambdaPlus m *
            (if m.Coprime n then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro m hmMem
      have hm : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hmMem).1
      have hmajor :
          main4WilsonOddNeutralizerMajorant P lambdaPlus m ≤
            main4WilsonNeutralizerMajorant P lambdaPlus m := by
        unfold main4WilsonOddNeutralizerMajorant
        by_cases hodd : Odd m
        · simp [hodd]
        · rw [if_neg hodd]
          exact main4WilsonNeutralizerMajorant_nonneg
            P m hP hm lambdaPlus hUpper
      exact mul_le_mul_of_nonneg_right hmajor (by positivity)
    _ = main4WilsonReciprocalDivisorCoprimeSieveSum
          P M n lambdaPlus :=
      sum_main4WilsonNeutralizerMajorant_coprimeIndicator_eq_sieveSum
        P M n hP.ne_zero lambdaPlus
    _ ≤ |main4WilsonReciprocalDivisorCoprimeSieveSum
          P M n lambdaPlus| := le_abs_self _

/-- Direct pointwise consequence of the one Lemma 2.2-style hypothesis. -/
theorem abs_wilsonJacobiCorrelation_oddNeutralizer_sq_le_of_coprimeUpperSieve
    (P M y n : ℕ) (hP : Squarefree P) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) (C : ℝ)
    (hSieve : Main4WilsonReciprocalDivisorCoprimeUpperSieveWith
      P M y lambdaPlus C)
    (hn : n ≠ 0) :
    |wilsonJacobiCorrelation
        (main4WilsonOddNeutralizerMajorant P lambdaPlus) M (n ^ 2)| ≤
      C * main4WilsonReciprocalDivisorCoprimeSieveScale P M y n := by
  rw [abs_of_nonneg
    (wilsonJacobiCorrelation_oddNeutralizer_sq_nonneg
      P M n hP lambdaPlus hUpper)]
  exact (wilsonJacobiCorrelation_oddNeutralizer_sq_le_abs_sieveSum
    P M n hP lambdaPlus hUpper).trans (hSieve n hn)

/-! ## Grouping square products by their square root -/

private def squareProductRoot (p : ℕ × ℕ) : ℕ :=
  Nat.sqrt (p.1 * p.2)

private theorem squareProductRoot_sq_eq
    {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ squareProductPairsUpTo N) :
    squareProductRoot p ^ 2 = p.1 * p.2 := by
  obtain ⟨_hpBox, hpSquare⟩ := Finset.mem_filter.mp hp
  obtain ⟨r, hr⟩ := (isSquare_iff_exists_sq (p.1 * p.2)).mp hpSquare
  exact (Nat.exists_mul_self' (p.1 * p.2)).mp ⟨r, hr.symm⟩

private theorem squareProductRoot_mem_Ioc
    {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ squareProductPairsUpTo N) :
    squareProductRoot p ∈ Finset.Ioc 0 N := by
  obtain ⟨hpBox, _hpSquare⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpBox
  obtain ⟨hp₁pos, hp₁N⟩ := Finset.mem_Icc.mp hp₁
  obtain ⟨hp₂pos, hp₂N⟩ := Finset.mem_Icc.mp hp₂
  apply Finset.mem_Ioc.mpr
  constructor
  · change 0 < Nat.sqrt (p.1 * p.2)
    exact Nat.sqrt_pos.mpr (Nat.mul_pos hp₁pos hp₂pos)
  · have hprod : p.1 * p.2 ≤ N ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hp₁N hp₂N
    have hsqrt := Nat.sqrt_le_sqrt hprod
    simpa [squareProductRoot] using hsqrt

private theorem card_squareProductRoot_fiber_le_divisors_sq
    (N r : ℕ) (hr : r ∈ Finset.Ioc 0 N) :
    ((squareProductPairsUpTo N).filter
        (fun p ↦ squareProductRoot p = r)).card ≤
      (r ^ 2).divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ p.1)
  · intro p hp
    obtain ⟨hpSquare, hpRoot⟩ := Finset.mem_filter.mp hp
    have hr0 : r ^ 2 ≠ 0 := pow_ne_zero 2
      (Nat.ne_of_gt (Finset.mem_Ioc.mp hr).1)
    apply Nat.mem_divisors.mpr
    refine ⟨⟨p.2, ?_⟩, hr0⟩
    rw [← hpRoot, squareProductRoot_sq_eq hpSquare]
  · intro p hp q hq hpq
    obtain ⟨hpSquare, hpRoot⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqSquare, hqRoot⟩ := Finset.mem_filter.mp hq
    have hp₁pos : 0 < p.1 := by
      exact (Finset.mem_Icc.mp
        (Finset.mem_product.mp
          (Finset.mem_filter.mp hpSquare).1).1).1
    apply Prod.ext hpq
    apply Nat.mul_left_cancel hp₁pos
    calc
      p.1 * p.2 = squareProductRoot p ^ 2 :=
        (squareProductRoot_sq_eq hpSquare).symm
      _ = r ^ 2 := by rw [hpRoot]
      _ = squareProductRoot q ^ 2 := by rw [hqRoot]
      _ = q.1 * q.2 := squareProductRoot_sq_eq hqSquare
      _ = p.1 * q.2 := by
        change p.1 = q.1 at hpq
        exact congrArg (fun x ↦ x * q.2) hpq.symm

/-- A nonnegative function of the square root can be summed over square
products at the cost of the exact divisor multiplicity `tau(r^2)`. -/
theorem sum_squareProductPairs_weight_root_le_divisor_sum
    (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ r ∈ Finset.Ioc 0 N, 0 ≤ F r) :
    ∑ p ∈ squareProductPairsUpTo N, F (squareProductRoot p) ≤
      ∑ r ∈ Finset.Ioc 0 N, ((r ^ 2).divisors.card : ℝ) * F r := by
  classical
  calc
    (∑ p ∈ squareProductPairsUpTo N, F (squareProductRoot p)) =
        ∑ r ∈ Finset.Ioc 0 N,
          ∑ p ∈ squareProductPairsUpTo N with squareProductRoot p = r,
            F (squareProductRoot p) := by
      rw [Finset.sum_fiberwise_of_maps_to
        (fun p hp ↦ squareProductRoot_mem_Ioc hp)]
    _ = ∑ r ∈ Finset.Ioc 0 N,
          (((squareProductPairsUpTo N).filter
            (fun p ↦ squareProductRoot p = r)).card : ℝ) * F r := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ p ∈ squareProductPairsUpTo N with squareProductRoot p = r,
            F (squareProductRoot p)) =
            ∑ _p ∈ (squareProductPairsUpTo N).filter
                (fun p ↦ squareProductRoot p = r), F r := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = (((squareProductPairsUpTo N).filter
              (fun p ↦ squareProductRoot p = r)).card : ℝ) * F r := by
          simp
    _ ≤ ∑ r ∈ Finset.Ioc 0 N,
          ((r ^ 2).divisors.card : ℝ) * F r := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (hF r hr)
      exact_mod_cast card_squareProductRoot_fiber_le_divisors_sq N r hr

/-! ## The complete square contribution -/

theorem main4WilsonReciprocalDivisorCoprimeSieveScale_nonneg
    (P M y n : ℕ) (hM : 2 ≤ M) (hn : n ≠ 0) :
    0 ≤ main4WilsonReciprocalDivisorCoprimeSieveScale P M y n := by
  have hlog : 0 < Real.log (M : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < M by omega)
  have hlocal :
      0 ≤ (n.totient : ℝ) / (n : ℝ) *
        main4WilsonReciprocalDivisorSieveFactor P n :=
    main4WilsonTotientRatio_mul_reciprocalDivisorSieveFactor_nonneg
      P n hn
  unfold main4WilsonReciprocalDivisorCoprimeSieveScale
  positivity

/-- The square part of Wilson's expanded odd-neutralizer moment, reduced to
the weighted divisor sum supplied by Lemma 2.2. -/
theorem abs_sum_square_wilsonOddNeutralizerCorrelation_le_divisorSieveSum
    (a : ℕ → ℝ) (P M N y : ℕ) (lambdaPlus : ℕ → ℝ) (C : ℝ)
    (hM : 2 ≤ M) (hP : Squarefree P)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (ha : main4OddSupportedUnitBound a) (hC : 0 ≤ C)
    (hSieve : Main4WilsonReciprocalDivisorCoprimeUpperSieveWith
      P M y lambdaPlus C) :
    |∑ p ∈ squareProductPairsUpTo N,
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤
      ∑ n ∈ Finset.Ioc 0 N,
        ((n ^ 2).divisors.card : ℝ) *
          (C * main4WilsonReciprocalDivisorCoprimeSieveScale P M y n) := by
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
    _ ≤ ∑ p ∈ squareProductPairsUpTo N,
          C * main4WilsonReciprocalDivisorCoprimeSieveScale
            P M y (squareProductRoot p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hroot0 : squareProductRoot p ≠ 0 :=
        Nat.ne_of_gt (Finset.mem_Ioc.mp (squareProductRoot_mem_Ioc hp)).1
      have hc :=
        abs_wilsonJacobiCorrelation_oddNeutralizer_sq_le_of_coprimeUpperSieve
          P M y (squareProductRoot p) hP lambdaPlus hUpper C hSieve hroot0
      rw [squareProductRoot_sq_eq hp] at hc
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
              (C * main4WilsonReciprocalDivisorCoprimeSieveScale
                P M y (squareProductRoot p)) := by
          gcongr
          · exact ha.2 p.1
          · exact ha.2 p.2
        _ = C * main4WilsonReciprocalDivisorCoprimeSieveScale
              P M y (squareProductRoot p) := by ring
    _ ≤ ∑ n ∈ Finset.Ioc 0 N,
          ((n ^ 2).divisors.card : ℝ) *
            (C * main4WilsonReciprocalDivisorCoprimeSieveScale P M y n) := by
      apply sum_squareProductPairs_weight_root_le_divisor_sum N
        (fun n ↦ C *
          main4WilsonReciprocalDivisorCoprimeSieveScale P M y n)
      intro n hn
      exact mul_nonneg hC
        (main4WilsonReciprocalDivisorCoprimeSieveScale_nonneg
          P M y n hM (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1))

/-- The full square aggregate downstream of Wilson's Lemma 2.2.  This is the
shortest source-faithful trust boundary for the square branch: the only
analytic hypothesis is `hSieve`; the factors `phi(n)/n * g_P(n)` and both
divisor sums are discharged inside Lean. -/
theorem abs_sum_square_wilsonOddNeutralizerCorrelation_le_of_coprimeUpperSieve
    (a : ℕ → ℝ) (P M N y : ℕ) (lambdaPlus : ℕ → ℝ) (C : ℝ)
    (hM : 2 ≤ M) (hP : Squarefree P)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (ha : main4OddSupportedUnitBound a) (hC : 0 ≤ C)
    (hSieve : Main4WilsonReciprocalDivisorCoprimeUpperSieveWith
      P M y lambdaPlus C) :
    |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun p ↦ IsSquare (p.1 * p.2)),
      a p.1 * a p.2 *
        wilsonJacobiCorrelation
          (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
          (p.1 * p.2)| ≤
      C *
        ((M : ℝ) / Real.sqrt (Real.log (M : ℝ)) *
            ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2) +
          (y : ℝ) *
            ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5)) := by
  have hraw :=
    abs_sum_square_wilsonOddNeutralizerCorrelation_le_divisorSieveSum
      a P M N y lambdaPlus C hM hP hUpper ha hC hSieve
  rw [show ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p ↦ IsSquare (p.1 * p.2)) = squareProductPairsUpTo N by rfl]
  apply hraw.trans
  let A : ℝ := (M : ℝ) / Real.sqrt (Real.log (M : ℝ))
  let Smain : ℝ :=
    ∑ n ∈ Finset.Ioc 0 N,
      ((n ^ 2).divisors.card : ℝ) *
        ((n.totient : ℝ) / (n : ℝ) *
          main4WilsonReciprocalDivisorSieveFactor P n)
  let Serr : ℝ :=
    ∑ n ∈ Finset.Ioc 0 N,
      ((n ^ 2).divisors.card : ℝ) * (n.divisors.card : ℝ)
  have hA : 0 ≤ A := by
    have hlog : 0 < Real.log (M : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < M by omega)
    dsimp [A]
    positivity
  have hmain :
      Smain ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
    exact sum_Ioc_card_divisors_sq_mul_totientRatio_sieveFactor_le P N
  have herr :
      Serr ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 := by
    exact sum_Ioc_card_divisors_sq_mul_card_divisors_real_le N
  have hsplit :
      (∑ n ∈ Finset.Ioc 0 N,
        ((n ^ 2).divisors.card : ℝ) *
          (C * main4WilsonReciprocalDivisorCoprimeSieveScale P M y n)) =
        C * A * Smain + C * (y : ℝ) * Serr := by
    dsimp only [main4WilsonReciprocalDivisorCoprimeSieveScale]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    dsimp only [A, Smain, Serr]
    apply congrArg₂ (· + ·)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
  rw [hsplit]
  calc
    C * A * Smain + C * (y : ℝ) * Serr ≤
        C * A * ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2) +
          C * (y : ℝ) *
            ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmain (mul_nonneg hC hA))
        (mul_le_mul_of_nonneg_left herr
          (mul_nonneg hC (Nat.cast_nonneg y)))
    _ = C *
        ((M : ℝ) / Real.sqrt (Real.log (M : ℝ)) *
            ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2) +
          (y : ℝ) *
            ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5)) := by
      dsimp [A]
      ring


end

end PellPaper
