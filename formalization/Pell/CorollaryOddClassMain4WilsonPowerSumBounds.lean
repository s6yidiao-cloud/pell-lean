import Pell.CorollaryOddClassMain4WilsonCombinedPrefix
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Elementary power-sum bounds for the Wilson Abel synthesis

This module contains only real-analysis estimates for finite natural
sums.  The constants are deliberately coarse: the application needs only
that the two error exponents are strictly below one.
-/

namespace PellPaper

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-- A fixed convergent-series constant for the low Wilson range. -/
def main4WilsonLowFirstSeriesConstant : ℝ :=
  ∑' n : ℕ, 4 * (n : ℝ) ^ (-5 / 4 : ℝ)

private theorem summable_main4WilsonLowFirstSeries :
    Summable (fun n : ℕ ↦ 4 * (n : ℝ) ^ (-5 / 4 : ℝ)) := by
  exact Summable.mul_left 4
    ((Real.summable_nat_rpow (p := (-5 / 4 : ℝ))).mpr (by norm_num))

theorem main4WilsonLowFirstSeriesConstant_nonneg :
    0 ≤ main4WilsonLowFirstSeriesConstant := by
  unfold main4WilsonLowFirstSeriesConstant
  exact tsum_nonneg fun n ↦ mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- A shifted version of the same convergent majorant, with a deliberately
coarse coefficient that also covers the `max 2` endpoint at `r = 1`. -/
def main4WilsonLowShiftedSeriesConstant : ℝ :=
  ∑' j : ℕ, 8 * (((j + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))

private theorem summable_main4WilsonLowShiftedSeries :
    Summable (fun j : ℕ ↦
      8 * (((j + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))) := by
  have hbase : Summable (fun n : ℕ ↦
      8 * (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Summable.mul_left 8
      ((Real.summable_nat_rpow (p := (-5 / 4 : ℝ))).mpr (by norm_num))
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr hbase

theorem main4WilsonLowShiftedSeriesConstant_nonneg :
    0 ≤ main4WilsonLowShiftedSeriesConstant := by
  unfold main4WilsonLowShiftedSeriesConstant
  exact tsum_nonneg fun j ↦ mul_nonneg (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem log_mul_rpow_neg_three_halves_le_lowSeriesTerm (n : ℕ) :
    Real.log (n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ) ≤
      4 * (n : ℝ) ^ (-5 / 4 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 4 by norm_num)
  have hlog' : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hlog
      _ = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
  have hpow :
      (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ) =
        (n : ℝ) ^ (-5 / 4 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    norm_num
  calc
    Real.log (n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ) ≤
        (4 * (n : ℝ) ^ (1 / 4 : ℝ)) *
          (n : ℝ) ^ (-3 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact hlog'
      · exact Real.rpow_nonneg hnpos.le _
    _ = 4 * (n : ℝ) ^ (-5 / 4 : ℝ) := by rw [mul_assoc, hpow]

/-- Every finite low-range logarithmic `p`-sum is bounded by one fixed
constant. -/
theorem sum_log_mul_rpow_neg_three_halves_le_lowSeriesConstant
    (s : Finset ℕ) :
    (∑ n ∈ s,
        Real.log (n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ)) ≤
      main4WilsonLowFirstSeriesConstant := by
  unfold main4WilsonLowFirstSeriesConstant
  calc
    (∑ n ∈ s,
        Real.log (n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ)) ≤
        ∑ n ∈ s, 4 * (n : ℝ) ^ (-5 / 4 : ℝ) := by
      exact Finset.sum_le_sum fun n _ ↦
        log_mul_rpow_neg_three_halves_le_lowSeriesTerm n
    _ ≤ ∑' n : ℕ, 4 * (n : ℝ) ^ (-5 / 4 : ℝ) := by
      exact summable_main4WilsonLowFirstSeries.sum_le_tsum s
        (fun n _ ↦ mul_nonneg (by norm_num)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- The elementary integral-test bound for the reciprocal square-root sum.
The range coordinates are those used by the Abel kernel. -/
theorem sum_range_succ_rpow_neg_half_le_two_sqrt (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) ≤
      2 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-1 / 2 : ℝ)
  have hanti : AntitoneOn f (Set.Icc 1 (1 + (k : ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show (-1 / 2 : ℝ) ≤ 0 by norm_num)).mono (by
        intro x hx
        exact (show (0 : ℝ) < x by linarith [hx.1]))
  have htail := hanti.sum_le_integral
  rw [integral_rpow (a := (1 : ℝ)) (b := 1 + (k : ℝ))
    (Or.inl (show (-1 : ℝ) < -1 / 2 by norm_num))] at htail
  have hrewrite :
      (∑ i ∈ Finset.range k, f (1 + ((i + 1 : ℕ) : ℝ))) =
        ∑ i ∈ Finset.range k,
          (((i + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [f]
    congr 2
    norm_num
    ring
  rw [hrewrite] at htail
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.cast_one, Real.one_rpow]
  rw [Real.sqrt_eq_rpow]
  have hkcast : (1 : ℝ) + (k : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hkcast] at htail
  have hshift :
      (∑ i ∈ Finset.range k,
          (((i + 1 + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) =
        ∑ i ∈ Finset.range k,
          (((i + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 3
  rw [hshift]
  have htail' :
      (∑ i ∈ Finset.range k,
          (((i + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) ≤
        2 * (((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) - 2 := by
    convert htail using 1
    all_goals norm_num [Nat.cast_add, Nat.cast_one, neg_div]
    all_goals ring
  linarith

/-- A tail of the `7/6` p-series beginning strictly above `S` is bounded
by the exact integral-test scale `6*S^(-1/6)`. -/
theorem sum_filter_range_succ_rpow_neg_seven_six_le
    (S N : ℕ) (hS : 1 ≤ S) :
    (∑ j ∈ (Finset.range N).filter (fun j ↦ S < j + 1),
        (((j + 1 : ℕ) : ℝ) ^ (-7 / 6 : ℝ))) ≤
      6 * (S : ℝ) ^ (-1 / 6 : ℝ) := by
  have hset :
      (Finset.range N).filter (fun j ↦ S < j + 1) =
        Finset.Ico S N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]
  let f : ℝ → ℝ := fun x ↦ x ^ (-7 / 6 : ℝ)
  have hSpos : (0 : ℝ) < S := by exact_mod_cast Nat.zero_lt_of_lt hS
  have hanti : AntitoneOn f (Set.Icc (S : ℝ) (N : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show (-7 / 6 : ℝ) ≤ 0 by norm_num)).mono (by
        intro x hx
        exact (show (0 : ℝ) < x by linarith [hx.1]))
  have hintegrable : IntegrableOn f (Set.Ioi (S : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt
      (show (-7 / 6 : ℝ) < -1 by norm_num) hSpos
  have hnonneg : ∀ t ∈ Set.Ioi (S : ℝ), 0 ≤ f t := by
    intro t ht
    exact Real.rpow_nonneg (hSpos.trans ht).le _
  have htail := hanti.sum_Ico_le_integral hintegrable hnonneg
  rw [integral_Ioi_rpow_of_lt
    (show (-7 / 6 : ℝ) < -1 by norm_num) hSpos] at htail
  have hexponent : (-7 / 6 : ℝ) + 1 = -1 / 6 := by norm_num
  rw [hexponent] at htail
  have htail' :
      (∑ j ∈ Finset.Ico S N,
          (((j + 1 : ℕ) : ℝ) ^ (-7 / 6 : ℝ))) ≤
        -((S : ℝ) ^ (-1 / 6 : ℝ) / (-1 / 6 : ℝ)) := by
    simpa only [f, Nat.cast_add, Nat.cast_one, neg_div] using htail
  calc
    (∑ j ∈ Finset.Ico S N,
        (((j + 1 : ℕ) : ℝ) ^ (-7 / 6 : ℝ))) ≤
        -((S : ℝ) ^ (-1 / 6 : ℝ) / (-1 / 6 : ℝ)) := htail'
    _ = 6 * (S : ℝ) ^ (-1 / 6 : ℝ) := by ring

/-- A filtered harmonic tail is bounded by the usual `1 + log N`
majorant for the complete harmonic sum. -/
theorem sum_filter_range_succ_inv_le_one_add_log (S N : ℕ) :
    (∑ j ∈ (Finset.range N).filter (fun j ↦ S < j + 1),
        (((j + 1 : ℕ) : ℝ))⁻¹) ≤
      1 + Real.log (N : ℝ) := by
  calc
    (∑ j ∈ (Finset.range N).filter (fun j ↦ S < j + 1),
        (((j + 1 : ℕ) : ℝ))⁻¹) ≤
        ∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ))⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (harmonic N : ℝ) := by
      unfold harmonic
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N

/-! ## Denominator reductions for the Abel kernel -/

private theorem natCast_rpow_div_mul_succ_le_rpow_sub_two
    (r : ℕ) (hr : 1 ≤ r) (a : ℝ) :
    (r : ℝ) ^ a /
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
      (r : ℝ) ^ (a - 2) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.zero_lt_of_lt hr
  have hsucc : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ r
  calc
    (r : ℝ) ^ a / ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
        (r : ℝ) ^ a / ((r : ℝ) * (r : ℝ)) := by
      exact div_le_div_of_nonneg_left
        (Real.rpow_nonneg hrpos.le a) (mul_pos hrpos hrpos)
        (mul_le_mul_of_nonneg_left hsucc hrpos.le)
    _ = (r : ℝ) ^ (a - 2) := by
      rw [← pow_two, ← Real.rpow_two, ← Real.rpow_sub hrpos]

/-- The first Wilson numerator over the Abel denominator has the summable
`r^(-3/2) log r` profile. -/
theorem sqrt_mul_log_div_natCast_mul_succ_le
    (r : ℕ) (hr : 1 ≤ r) :
    Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
      Real.log (r : ℝ) * (r : ℝ) ^ (-3 / 2 : ℝ) := by
  have hlog : 0 ≤ Real.log (r : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hr)
  rw [Real.sqrt_eq_rpow]
  calc
    (r : ℝ) ^ (1 / 2 : ℝ) * Real.log (r : ℝ) /
          ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) =
        Real.log (r : ℝ) *
          ((r : ℝ) ^ (1 / 2 : ℝ) /
            ((r : ℝ) * (((r + 1 : ℕ) : ℝ)))) := by ring
    _ ≤ Real.log (r : ℝ) * (r : ℝ) ^ ((1 / 2 : ℝ) - 2) :=
      mul_le_mul_of_nonneg_left
        (natCast_rpow_div_mul_succ_le_rpow_sub_two r hr (1 / 2 : ℝ)) hlog
    _ = Real.log (r : ℝ) * (r : ℝ) ^ (-3 / 2 : ℝ) := by norm_num

/-- The second Wilson numerator over the Abel denominator has the
`r^(-1/2) sqrt(log r)` profile. -/
theorem rpow_three_halves_mul_sqrt_log_div_natCast_mul_succ_le
    (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (r : ℝ)) /
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
      Real.sqrt (Real.log (r : ℝ)) *
        (r : ℝ) ^ (-1 / 2 : ℝ) := by
  calc
    (r : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (r : ℝ)) /
          ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) =
        Real.sqrt (Real.log (r : ℝ)) *
          ((r : ℝ) ^ (3 / 2 : ℝ) /
            ((r : ℝ) * (((r + 1 : ℕ) : ℝ)))) := by ring
    _ ≤ Real.sqrt (Real.log (r : ℝ)) *
        (r : ℝ) ^ ((3 / 2 : ℝ) - 2) :=
      mul_le_mul_of_nonneg_left
        (natCast_rpow_div_mul_succ_le_rpow_sub_two r hr (3 / 2 : ℝ))
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (Real.log (r : ℝ)) *
        (r : ℝ) ^ (-1 / 2 : ℝ) := by norm_num

/-- The first Friedlander--Iwaniec numerator over the Abel denominator has
the tail-summable `r^(-7/6)` profile. -/
theorem rpow_five_sixths_div_natCast_mul_succ_le
    (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) ^ (5 / 6 : ℝ) /
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
      (r : ℝ) ^ (-7 / 6 : ℝ) := by
  convert natCast_rpow_div_mul_succ_le_rpow_sub_two
    r hr (5 / 6 : ℝ) using 1
  norm_num

/-- The linear Friedlander--Iwaniec numerator over the Abel denominator is
at most `1/r`. -/
theorem natCast_div_natCast_mul_succ_le_inv
    (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) /
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
      ((r : ℝ))⁻¹ := by
  have h := natCast_rpow_div_mul_succ_le_rpow_sub_two r hr (1 : ℝ)
  norm_num at h
  simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_neg_one] using h

/-! ## Sum-ready bounds, including the length-one endpoint -/

/-- The `max 2` used to estimate the first prefix still leaves a uniformly
summable first Wilson profile. -/
theorem sqrt_max_two_mul_log_div_natCast_mul_succ_le_shiftedSeriesTerm
    (r : ℕ) (hr : 1 ≤ r) :
    Real.sqrt ((max 2 r : ℕ) : ℝ) *
          Real.log ((max 2 r : ℕ) : ℝ) /
        ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
      8 * (r : ℝ) ^ (-5 / 4 : ℝ) := by
  by_cases hrTwo : 2 ≤ r
  · rw [max_eq_right hrTwo]
    calc
      Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
          ((r : ℝ) * (((r + 1 : ℕ) : ℝ))) ≤
          Real.log (r : ℝ) * (r : ℝ) ^ (-3 / 2 : ℝ) :=
        sqrt_mul_log_div_natCast_mul_succ_le r hr
      _ ≤ 4 * (r : ℝ) ^ (-5 / 4 : ℝ) :=
        log_mul_rpow_neg_three_halves_le_lowSeriesTerm r
      _ ≤ 8 * (r : ℝ) ^ (-5 / 4 : ℝ) := by
        have hpow := Real.rpow_nonneg (Nat.cast_nonneg r) (-5 / 4 : ℝ)
        linarith
  · have hrOne : r = 1 := by omega
    subst r
    have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hlog : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hprod : Real.sqrt (2 : ℝ) * Real.log (2 : ℝ) ≤ 2 := by
      simpa only [mul_one] using
        (mul_le_mul hsqrt hlog (Real.log_nonneg (by norm_num))
          (by norm_num : (0 : ℝ) ≤ 2))
    norm_num only [max_eq_left, Nat.cast_ofNat, Real.one_rpow]
    linarith

/-- Any finite set of Abel coordinates has its first `max 2` Wilson profile
bounded by one fixed constant. -/
theorem sum_sqrt_max_two_mul_log_div_le_shiftedSeriesConstant
    (s : Finset ℕ) :
    (∑ j ∈ s,
        Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
            Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
      main4WilsonLowShiftedSeriesConstant := by
  unfold main4WilsonLowShiftedSeriesConstant
  calc
    (∑ j ∈ s,
        Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
            Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        ∑ j ∈ s, 8 * (((j + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
      exact Finset.sum_le_sum fun j _ ↦ by
        simpa only [Nat.add_assoc] using
          sqrt_max_two_mul_log_div_natCast_mul_succ_le_shiftedSeriesTerm
            (j + 1) (by omega)
    _ ≤ ∑' j : ℕ, 8 * (((j + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
      exact summable_main4WilsonLowShiftedSeries.sum_le_tsum s
        (fun j _ ↦ mul_nonneg (by norm_num)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- If all low coordinates have logarithm at most `log X`, then their
second Wilson profile is controlled by the elementary square-root sum. -/
theorem sum_low_max_two_secondWilsonProfile_le
    (X : ℝ) (S N : ℕ)
    (hlog : ∀ j ∈ (Finset.range N).filter (fun j ↦ j + 1 ≤ S),
      Real.log ((max 2 (j + 1) : ℕ) : ℝ) ≤ Real.log X) :
    (∑ j ∈ (Finset.range N).filter (fun j ↦ j + 1 ≤ S),
        ((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
            Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
      8 * Real.sqrt (Real.log X) *
        Real.sqrt ((S + 1 : ℕ) : ℝ) := by
  let s := (Finset.range N).filter (fun j ↦ j + 1 ≤ S)
  have hsSubset : s ⊆ Finset.range (S + 1) := by
    intro j hj
    have hjS : j + 1 ≤ S := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_range]
    omega
  have hsqrtLogX : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  calc
    (∑ j ∈ (Finset.range N).filter (fun j ↦ j + 1 ≤ S),
        ((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
            Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        ∑ j ∈ s, 4 * Real.sqrt (Real.log X) *
          (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjmem : j ∈ (Finset.range N).filter (fun j ↦ j + 1 ≤ S) := hj
      have hsqrtLog :
          Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) ≤
            Real.sqrt (Real.log X) := Real.sqrt_le_sqrt (hlog j hjmem)
      by_cases hjTwo : 2 ≤ j + 1
      · rw [max_eq_right hjTwo]
        have hsqrtLog' :
            Real.sqrt (Real.log ((j + 1 : ℕ) : ℝ)) ≤
              Real.sqrt (Real.log X) := by
          simpa only [max_eq_right hjTwo] using hsqrtLog
        calc
          ((j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
                Real.sqrt (Real.log ((j + 1 : ℕ) : ℝ)) /
              ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) ≤
              Real.sqrt (Real.log ((j + 1 : ℕ) : ℝ)) *
                (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
            simpa only [Nat.add_assoc] using
              rpow_three_halves_mul_sqrt_log_div_natCast_mul_succ_le
                (j + 1) (by omega)
          _ ≤ Real.sqrt (Real.log X) *
                (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hsqrtLog'
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          _ ≤ 4 * Real.sqrt (Real.log X) *
                (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
            have hpow := Real.rpow_nonneg
              (Nat.cast_nonneg (j + 1)) (-1 / 2 : ℝ)
            nlinarith
      · have hjZero : j = 0 := by omega
        subst j
        have hpowTwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
          calc
            (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := by norm_num [Real.rpow_two]
        have hprod :
            (2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log 2) ≤
              4 * Real.sqrt (Real.log X) :=
          mul_le_mul hpowTwo hsqrtLog (Real.sqrt_nonneg _)
            (by norm_num)
        norm_num only [Nat.zero_add, Nat.cast_one, Nat.cast_ofNat,
          max_eq_left, Real.one_rpow]
        nlinarith
    _ ≤ ∑ j ∈ Finset.range (S + 1),
          4 * Real.sqrt (Real.log X) *
            (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsSubset
        (fun _ _ _ ↦ mul_nonneg
          (mul_nonneg (by norm_num) hsqrtLogX)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = 4 * Real.sqrt (Real.log X) *
          (∑ j ∈ Finset.range (S + 1),
            (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * Real.sqrt (Real.log X) *
          (2 * Real.sqrt ((S + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_range_succ_rpow_neg_half_le_two_sqrt S)
        (mul_nonneg (by norm_num) hsqrtLogX)
    _ = 8 * Real.sqrt (Real.log X) *
          Real.sqrt ((S + 1 : ℕ) : ℝ) := by ring

end

end PellPaper
