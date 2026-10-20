import Pell.CorollaryOddClassMain4WilsonPowerSumBounds
import Pell.CorollaryOddClassMain4WilsonScaleEnvelope
import Pell.CorollaryOddClassMain4WilsonLogAbsorption

/-!
# Summing the low and high Main4 rectangle envelopes

This module combines the pointwise rectangle envelopes with the
elementary power-sum estimates.  The first section is independent of the
rectangle definitions and records the exact Friedlander--Iwaniec profile
summation used by the high Abel range.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-! ## Common large-cutoff facts -/

theorem main4Wilson_one_le_log_of_large {X : ℝ} (hX : 64 ≤ X) :
    1 ≤ Real.log X := by
  have hexpX : Real.exp 1 ≤ X := by
    linarith [Real.exp_one_lt_three]
  have hlog := Real.log_le_log (Real.exp_pos 1) hexpX
  simpa only [Real.log_exp] using hlog

theorem main4Wilson_splitPoint_le_terminalEndpoint
    {X : ℝ} (hX : 64 ≤ X) :
    main4WilsonAbelSplitPoint X ≤ ⌈X⌉₊ ^ 2 := by
  have hX0 : 0 ≤ X := by linarith
  have hS := (main4Wilson_ceilSqrt_bounds hX).2
  have htwoSqrt : 2 * Real.sqrt X ≤ X := by
    nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
  have hY := (main4Wilson_ceilX_bounds hX).1
  have hYnonneg : 0 ≤ (⌈X⌉₊ : ℝ) := Nat.cast_nonneg _
  have hYone : (1 : ℝ) ≤ (⌈X⌉₊ : ℝ) := by linarith
  have hYSq : (⌈X⌉₊ : ℝ) ≤ (⌈X⌉₊ : ℝ) ^ 2 := by nlinarith
  have hreal : (main4WilsonAbelSplitPoint X : ℝ) ≤
      ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_pow]
    linarith
  exact_mod_cast hreal

/-- The two Friedlander--Iwaniec powers, after division by the Abel kernel,
sum to a p-series tail and a harmonic tail. -/
theorem sum_filter_range_succ_friedlanderIwaniecProfile_le
    (A B : ℝ) (S N : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 1 ≤ S) :
    (∑ j ∈ (Finset.range N).filter (fun j ↦ S < j + 1),
        (A * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
            B * (((j + 1 : ℕ) : ℝ))) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
      A * (6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
        B * (1 + Real.log (N : ℝ)) := by
  let s := (Finset.range N).filter (fun j ↦ S < j + 1)
  calc
    (∑ j ∈ (Finset.range N).filter (fun j ↦ S < j + 1),
        (A * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
            B * (((j + 1 : ℕ) : ℝ))) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        ∑ j ∈ s,
          (A * (((j + 1 : ℕ) : ℝ) ^ (-7 / 6 : ℝ)) +
            B * ((((j + 1 : ℕ) : ℝ))⁻¹)) := by
      apply Finset.sum_le_sum
      intro j _
      have hr : 1 ≤ j + 1 := by omega
      calc
        (A * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
              B * (((j + 1 : ℕ) : ℝ))) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) =
            A * ((((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) /
                ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) +
              B * ((((j + 1 : ℕ) : ℝ)) /
                ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) := by ring
        _ ≤ A * (((j + 1 : ℕ) : ℝ) ^ (-7 / 6 : ℝ)) +
              B * ((((j + 1 : ℕ) : ℝ))⁻¹) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (by
                simpa only [Nat.add_assoc] using
                  rpow_five_sixths_div_natCast_mul_succ_le (j + 1) hr)
              hA)
            (mul_le_mul_of_nonneg_left
              (by
                simpa only [Nat.add_assoc] using
                  natCast_div_natCast_mul_succ_le_inv (j + 1) hr)
              hB)
    _ = A * (∑ j ∈ s,
          (((j + 1 : ℕ) : ℝ) ^ (-7 / 6 : ℝ))) +
        B * (∑ j ∈ s, ((((j + 1 : ℕ) : ℝ))⁻¹)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * (6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
        B * (1 + Real.log (N : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (sum_filter_range_succ_rpow_neg_seven_six_le S N hS) hA)
        (mul_le_mul_of_nonneg_left
          (sum_filter_range_succ_inv_le_one_add_log S N) hB)

/-- At the terminal Abel endpoint the same two powers simplify exactly
after division by the endpoint. -/
theorem friedlanderIwaniecProfile_div_terminal
    (A B : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (A * (N : ℝ) ^ (5 / 6 : ℝ) + B * (N : ℝ)) / (N : ℝ) =
      A * (N : ℝ) ^ (-1 / 6 : ℝ) + B := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN
  have hpow :
      (N : ℝ) ^ (5 / 6 : ℝ) / (N : ℝ) =
        (N : ℝ) ^ (-1 / 6 : ℝ) := by
    calc
      (N : ℝ) ^ (5 / 6 : ℝ) / (N : ℝ) =
          (N : ℝ) ^ ((5 / 6 : ℝ) - 1) :=
        (Real.rpow_sub_one hNpos.ne' (5 / 6 : ℝ)).symm
      _ = (N : ℝ) ^ (-1 / 6 : ℝ) := by norm_num
  calc
    (A * (N : ℝ) ^ (5 / 6 : ℝ) + B * (N : ℝ)) / (N : ℝ) =
        A * ((N : ℝ) ^ (5 / 6 : ℝ) / (N : ℝ)) +
          B * ((N : ℝ) / (N : ℝ)) := by ring
    _ = A * (N : ℝ) ^ (-1 / 6 : ℝ) + B := by
      rw [hpow, div_self hNpos.ne']
      ring

/-! ## The complete low Wilson scale -/

/-- Before simplifying powers, the low Wilson scale is bounded by the two
elementary finite sums proved in the preceding module. -/
theorem main4WilsonLowAbelRectangleScale_le_series_envelope
    {X : ℝ} (hX : 64 ≤ X) :
    main4WilsonLowAbelRectangleScale X ≤
      16 *
        ((X / Real.sqrt (Real.log X)) *
            main4WilsonLowShiftedSeriesConstant +
          (X ^ (2 / 3 : ℝ) /
              (Real.log X) ^ (1 / 4 : ℝ)) *
            (8 * Real.sqrt (Real.log X) *
              Real.sqrt ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ))) := by
  let T := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  let s := (Finset.range (T - 1)).filter (fun j ↦ j + 1 ≤ S)
  have hST : S ≤ T := main4Wilson_splitPoint_le_terminalEndpoint hX
  have hTtwo : 2 ≤ T := main4Wilson_terminalEndpoint_two_le (by linarith)
  have hlog : ∀ j ∈ s,
      Real.log ((max 2 (j + 1) : ℕ) : ℝ) ≤ Real.log X := by
    intro j hj
    exact main4Wilson_log_max_two_le_logX_of_le_splitPoint hX
      (Finset.mem_filter.mp hj).2
  have hfirst :
      (∑ j ∈ s,
          Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
              Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        main4WilsonLowShiftedSeriesConstant :=
    sum_sqrt_max_two_mul_log_div_le_shiftedSeriesConstant s
  have hsecond :
      (∑ j ∈ s,
          ((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
              Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        8 * Real.sqrt (Real.log X) *
          Real.sqrt ((S + 1 : ℕ) : ℝ) := by
    exact sum_low_max_two_secondWilsonProfile_le X S (T - 1) hlog
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hcoefOne : 0 ≤ X / Real.sqrt (Real.log X) := by positivity
  have hcoefTwo :
      0 ≤ X ^ (2 / 3 : ℝ) / (Real.log X) ^ (1 / 4 : ℝ) := by
    positivity
  unfold main4WilsonLowAbelRectangleScale
  dsimp only
  change (∑ j ∈ s,
      main4WilsonFourTwistRectangleScale X (max 2 (j + 1)) /
        ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤ _
  calc
    (∑ j ∈ s,
        main4WilsonFourTwistRectangleScale X (max 2 (j + 1)) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        ∑ j ∈ s, 16 *
          ((X / Real.sqrt (Real.log X)) *
              (Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
                Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
                  ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) +
            (X ^ (2 / 3 : ℝ) /
                (Real.log X) ^ (1 / 4 : ℝ)) *
              (((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
                Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
                  ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjS : j + 1 ≤ S := (Finset.mem_filter.mp hj).2
      have hrTwo : 2 ≤ max 2 (j + 1) := le_max_left _ _
      have hrTop : max 2 (j + 1) ≤ T := by
        exact max_le hTtwo (hjS.trans hST)
      have hscale := main4WilsonFourTwistRectangleScale_le_explicit
        hX hrTwo hrTop
      have hden : 0 ≤
          (((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)) := by positivity
      calc
        main4WilsonFourTwistRectangleScale X (max 2 (j + 1)) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) ≤
            (16 *
              (X * Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
                    Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
                    Real.sqrt (Real.log X) +
                X ^ (2 / 3 : ℝ) *
                    ((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
                    Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
                    (Real.log X) ^ (1 / 4 : ℝ))) /
              ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) :=
          div_le_div_of_nonneg_right hscale hden
        _ = 16 *
          ((X / Real.sqrt (Real.log X)) *
              (Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
                Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
                  ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) +
            (X ^ (2 / 3 : ℝ) /
                (Real.log X) ^ (1 / 4 : ℝ)) *
              (((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
                Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
                  ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))))) := by
          ring
    _ = 16 *
        ((X / Real.sqrt (Real.log X)) *
            (∑ j ∈ s,
              Real.sqrt ((max 2 (j + 1) : ℕ) : ℝ) *
                Real.log ((max 2 (j + 1) : ℕ) : ℝ) /
                  ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) +
          (X ^ (2 / 3 : ℝ) /
              (Real.log X) ^ (1 / 4 : ℝ)) *
            (∑ j ∈ s,
              ((max 2 (j + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
                Real.sqrt (Real.log ((max 2 (j + 1) : ℕ) : ℝ)) /
                  ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))))) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 16 *
        ((X / Real.sqrt (Real.log X)) *
            main4WilsonLowShiftedSeriesConstant +
          (X ^ (2 / 3 : ℝ) /
              (Real.log X) ^ (1 / 4 : ℝ)) *
            (8 * Real.sqrt (Real.log X) *
              Real.sqrt ((S + 1 : ℕ) : ℝ))) := by
      gcongr

/-- The low Wilson scale consists of a constant multiple of the target
scale and one lower-order `11/12` error. -/
theorem main4WilsonLowAbelRectangleScale_le_naturalScale_add_error
    {X : ℝ} (hX : 64 ≤ X) :
    main4WilsonLowAbelRectangleScale X ≤
      16 * main4WilsonLowShiftedSeriesConstant *
          (X / Real.sqrt (Real.log X)) +
        256 * X ^ (11 / 12 : ℝ) *
          (Real.log X) ^ (7 / 6 : ℝ) := by
  have hbase := main4WilsonLowAbelRectangleScale_le_series_envelope hX
  have hXpos : 0 < X := by linarith
  have hlogOne := main4Wilson_one_le_log_of_large hX
  have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  have hsplit := main4Wilson_sqrt_splitPoint_add_one_le hX
  have hXpower :
      X ^ (2 / 3 : ℝ) * X ^ (1 / 4 : ℝ) =
        X ^ (11 / 12 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hlogQuotient :
      Real.sqrt (Real.log X) /
          (Real.log X) ^ (1 / 4 : ℝ) =
        (Real.log X) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hlogPos]
    norm_num
  have hlogPower :
      (Real.log X) ^ (1 / 4 : ℝ) ≤
        (Real.log X) ^ (7 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  have herror :
      (X ^ (2 / 3 : ℝ) /
          (Real.log X) ^ (1 / 4 : ℝ)) *
        (8 * Real.sqrt (Real.log X) *
          Real.sqrt ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ)) ≤
      16 * X ^ (11 / 12 : ℝ) *
        (Real.log X) ^ (7 / 6 : ℝ) := by
    calc
      (X ^ (2 / 3 : ℝ) /
          (Real.log X) ^ (1 / 4 : ℝ)) *
          (8 * Real.sqrt (Real.log X) *
            Real.sqrt ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ)) ≤
          (X ^ (2 / 3 : ℝ) /
            (Real.log X) ^ (1 / 4 : ℝ)) *
            (8 * Real.sqrt (Real.log X) *
              (2 * X ^ (1 / 4 : ℝ))) := by
        gcongr
      _ = 16 * (X ^ (2 / 3 : ℝ) * X ^ (1 / 4 : ℝ)) *
          (Real.sqrt (Real.log X) /
            (Real.log X) ^ (1 / 4 : ℝ)) := by ring
      _ = 16 * X ^ (11 / 12 : ℝ) *
          (Real.log X) ^ (1 / 4 : ℝ) := by
        rw [hXpower, hlogQuotient]
      _ ≤ 16 * X ^ (11 / 12 : ℝ) *
          (Real.log X) ^ (7 / 6 : ℝ) := by
        gcongr
  calc
    main4WilsonLowAbelRectangleScale X ≤
        16 *
          ((X / Real.sqrt (Real.log X)) *
              main4WilsonLowShiftedSeriesConstant +
            (X ^ (2 / 3 : ℝ) /
                (Real.log X) ^ (1 / 4 : ℝ)) *
              (8 * Real.sqrt (Real.log X) *
                Real.sqrt ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ))) := hbase
    _ ≤ 16 *
          ((X / Real.sqrt (Real.log X)) *
              main4WilsonLowShiftedSeriesConstant +
            16 * X ^ (11 / 12 : ℝ) *
              (Real.log X) ^ (7 / 6 : ℝ)) := by
      gcongr
    _ = 16 * main4WilsonLowShiftedSeriesConstant *
          (X / Real.sqrt (Real.log X)) +
        256 * X ^ (11 / 12 : ℝ) *
          (Real.log X) ^ (7 / 6 : ℝ) := by ring

/-! ## The complete high Friedlander--Iwaniec scale -/

theorem main4Wilson_splitPoint_neg_sixth_le
    {X : ℝ} (hX : 64 ≤ X) :
    (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ) ≤
      X ^ (-1 / 12 : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hSlo := (main4Wilson_ceilSqrt_bounds hX).1
  calc
    (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ) ≤
        (Real.sqrt X) ^ (-1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hXpos) hSlo (by norm_num)
    _ = X ^ (-1 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
      norm_num

theorem main4Wilson_terminalEndpoint_neg_sixth_le_splitPoint
    {X : ℝ} (hX : 64 ≤ X) :
    (((⌈X⌉₊ ^ 2 : ℕ) : ℝ)) ^ (-1 / 6 : ℝ) ≤
      (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ) := by
  have hSpos : (0 : ℝ) < main4WilsonAbelSplitPoint X := by
    exact_mod_cast Nat.zero_lt_of_lt
      (main4WilsonAbelSplitPoint_two_le_of_large hX)
  have hST := main4Wilson_splitPoint_le_terminalEndpoint hX
  have hcast : (main4WilsonAbelSplitPoint X : ℝ) ≤
      ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hST
  exact Real.rpow_le_rpow_of_nonpos hSpos hcast (by norm_num)

theorem main4Wilson_log_terminalEndpoint_sub_one_le_four_log
    {X : ℝ} (hX : 64 ≤ X) :
    Real.log (((⌈X⌉₊ ^ 2 - 1 : ℕ) : ℝ)) ≤ 4 * Real.log X := by
  let Y := ⌈X⌉₊
  let T := Y ^ 2
  have hTtwo : 2 ≤ T := main4Wilson_terminalEndpoint_two_le (by linarith)
  have hYtwo : 2 ≤ Y := (main4Wilson_outerEndpoints_admissible (by linarith)).1
  have hsubpos : (0 : ℝ) < (T - 1 : ℕ) := by
    exact_mod_cast (show 0 < T - 1 by omega)
  have hsubArg : ((T - 1 : ℕ) : ℝ) ≤
      3 * (Y : ℝ) * (T : ℝ) := by
    have hsubT : ((T - 1 : ℕ) : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.sub_le T 1
    have hYcast : (2 : ℝ) ≤ Y := by exact_mod_cast hYtwo
    have hTcast : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    nlinarith
  have hlogSub : Real.log ((T - 1 : ℕ) : ℝ) ≤
      Real.log (3 * (Y : ℝ) * (T : ℝ)) :=
    Real.log_le_log hsubpos hsubArg
  obtain ⟨hYlo, hYhi⟩ := (main4Wilson_threeBranchCeil_geometry hX).1
  have hlogArg := main4FriedlanderIwaniec_branch_log_le_four_logX
    hX hYlo hYhi hTtwo (show T ≤ ⌈X⌉₊ ^ 2 by rfl)
  exact hlogSub.trans hlogArg

/-- Before simplifying powers, the high range is exactly controlled by a
p-series tail, a harmonic sum, and its terminal endpoint. -/
theorem main4FriedlanderIwaniecHighAbelRectangleScale_le_series_envelope
    {X : ℝ} (hX : 64 ≤ X) :
    main4FriedlanderIwaniecHighAbelRectangleScale X ≤
      128 * (Real.log X) ^ (7 / 6 : ℝ) *
        (X *
            ((((⌈X⌉₊ ^ 2 : ℕ) : ℝ) ^ (-1 / 6 : ℝ)) +
              6 * (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ)) +
          X ^ (5 / 6 : ℝ) *
            (2 + Real.log ((⌈X⌉₊ ^ 2 - 1 : ℕ) : ℝ))) := by
  let T := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  let s := (Finset.range (T - 1)).filter (fun j ↦ S < j + 1)
  have hTtwo : 2 ≤ T := main4Wilson_terminalEndpoint_two_le (by linarith)
  have hSone : 1 ≤ S := (main4WilsonAbelSplitPoint_two_le_of_large hX).trans' (by omega)
  have hlogPos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogPowNonneg : 0 ≤ (Real.log X) ^ (7 / 6 : ℝ) :=
    Real.rpow_nonneg hlogPos.le _
  have hterminal :
      main4FriedlanderIwaniecFourTwistRectangleScale X T / (T : ℝ) ≤
        128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (X * (T : ℝ) ^ (-1 / 6 : ℝ) + X ^ (5 / 6 : ℝ)) := by
    have hscale := main4FriedlanderIwaniecFourTwistRectangleScale_le_explicit
      hX hTtwo (show T ≤ ⌈X⌉₊ ^ 2 by rfl)
    calc
      main4FriedlanderIwaniecFourTwistRectangleScale X T / (T : ℝ) ≤
          (128 * (Real.log X) ^ (7 / 6 : ℝ) *
            (X * (T : ℝ) ^ (5 / 6 : ℝ) +
              X ^ (5 / 6 : ℝ) * (T : ℝ))) / (T : ℝ) :=
        div_le_div_of_nonneg_right hscale (Nat.cast_nonneg T)
      _ = 128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (X * (T : ℝ) ^ (-1 / 6 : ℝ) + X ^ (5 / 6 : ℝ)) := by
        have hprofile := friedlanderIwaniecProfile_div_terminal X
          (X ^ (5 / 6 : ℝ)) T (by omega)
        calc
          (128 * (Real.log X) ^ (7 / 6 : ℝ) *
              (X * (T : ℝ) ^ (5 / 6 : ℝ) +
                X ^ (5 / 6 : ℝ) * (T : ℝ))) / (T : ℝ) =
              128 * (Real.log X) ^ (7 / 6 : ℝ) *
                ((X * (T : ℝ) ^ (5 / 6 : ℝ) +
                  X ^ (5 / 6 : ℝ) * (T : ℝ)) / (T : ℝ)) := by ring
          _ = 128 * (Real.log X) ^ (7 / 6 : ℝ) *
              (X * (T : ℝ) ^ (-1 / 6 : ℝ) + X ^ (5 / 6 : ℝ)) := by
            rw [hprofile]
  have hsumProfile :=
    sum_filter_range_succ_friedlanderIwaniecProfile_le
      X (X ^ (5 / 6 : ℝ)) S (T - 1) (by linarith)
        (Real.rpow_nonneg (by linarith : 0 ≤ X) _) hSone
  have hsumProfile' :
      (∑ j ∈ s,
        (X * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
            X ^ (5 / 6 : ℝ) * (((j + 1 : ℕ) : ℝ))) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        X * (6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
          X ^ (5 / 6 : ℝ) *
            (1 + Real.log ((T - 1 : ℕ) : ℝ)) := by
    simpa only [s] using hsumProfile
  have hsum :
      (∑ j ∈ s,
          main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (X * (6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
            X ^ (5 / 6 : ℝ) *
              (1 + Real.log ((T - 1 : ℕ) : ℝ))) := by
    calc
      (∑ j ∈ s,
          main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
          ∑ j ∈ s,
            128 * (Real.log X) ^ (7 / 6 : ℝ) *
              ((X * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
                  X ^ (5 / 6 : ℝ) * (((j + 1 : ℕ) : ℝ))) /
                ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjAbove : S < j + 1 := (Finset.mem_filter.mp hj).2
        have hjRange : j < T - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hrTwo : 2 ≤ j + 1 := by omega
        have hrTop : j + 1 ≤ T := by omega
        have hscale := main4FriedlanderIwaniecFourTwistRectangleScale_le_explicit
          hX hrTwo hrTop
        calc
          main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
              ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) ≤
              (128 * (Real.log X) ^ (7 / 6 : ℝ) *
                (X * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
                  X ^ (5 / 6 : ℝ) * (((j + 1 : ℕ) : ℝ))) /
                ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) :=
            div_le_div_of_nonneg_right hscale (by positivity)
          _ = 128 * (Real.log X) ^ (7 / 6 : ℝ) *
              ((X * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
                  X ^ (5 / 6 : ℝ) * (((j + 1 : ℕ) : ℝ))) /
                ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) := by ring
      _ = 128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (∑ j ∈ s,
            (X * (((j + 1 : ℕ) : ℝ) ^ (5 / 6 : ℝ)) +
                X ^ (5 / 6 : ℝ) * (((j + 1 : ℕ) : ℝ))) /
              ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) := by
        rw [Finset.mul_sum]
      _ ≤ 128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (X * (6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
            X ^ (5 / 6 : ℝ) *
              (1 + Real.log ((T - 1 : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hsumProfile'
          (mul_nonneg (by norm_num) hlogPowNonneg)
  unfold main4FriedlanderIwaniecHighAbelRectangleScale
  dsimp only
  simp only [not_le]
  change
    main4FriedlanderIwaniecFourTwistRectangleScale X T / (T : ℝ) +
        (∑ j ∈ s,
          main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤ _
  calc
    main4FriedlanderIwaniecFourTwistRectangleScale X T / (T : ℝ) +
        (∑ j ∈ s,
          main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) ≤
        128 * (Real.log X) ^ (7 / 6 : ℝ) *
            (X * (T : ℝ) ^ (-1 / 6 : ℝ) + X ^ (5 / 6 : ℝ)) +
          128 * (Real.log X) ^ (7 / 6 : ℝ) *
            (X * (6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
              X ^ (5 / 6 : ℝ) *
                (1 + Real.log ((T - 1 : ℕ) : ℝ))) :=
      add_le_add hterminal hsum
    _ = 128 * (Real.log X) ^ (7 / 6 : ℝ) *
        (X * ((T : ℝ) ^ (-1 / 6 : ℝ) +
            6 * (S : ℝ) ^ (-1 / 6 : ℝ)) +
          X ^ (5 / 6 : ℝ) *
            (2 + Real.log ((T - 1 : ℕ) : ℝ))) := by ring

/-- The high Friedlander--Iwaniec scale has precisely the two lower-order
errors absorbed later by the Mathlib log-power estimates. -/
theorem main4FriedlanderIwaniecHighAbelRectangleScale_le_errors
    {X : ℝ} (hX : 64 ≤ X) :
    main4FriedlanderIwaniecHighAbelRectangleScale X ≤
      896 * X ^ (11 / 12 : ℝ) *
          (Real.log X) ^ (7 / 6 : ℝ) +
        768 * X ^ (5 / 6 : ℝ) *
          (Real.log X) ^ (13 / 6 : ℝ) := by
  have hbase :=
    main4FriedlanderIwaniecHighAbelRectangleScale_le_series_envelope hX
  have hXpos : 0 < X := by linarith
  have hlogOne := main4Wilson_one_le_log_of_large hX
  have hlogNonneg : 0 ≤ Real.log X := le_trans zero_le_one hlogOne
  have hterminal := main4Wilson_terminalEndpoint_neg_sixth_le_splitPoint hX
  have hsplit := main4Wilson_splitPoint_neg_sixth_le hX
  have hlogTerminal := main4Wilson_log_terminalEndpoint_sub_one_le_four_log hX
  have hfirstPower :
      X * X ^ (-1 / 12 : ℝ) = X ^ (11 / 12 : ℝ) := by
    calc
      X * X ^ (-1 / 12 : ℝ) =
          X ^ (1 : ℝ) * X ^ (-1 / 12 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (-1 / 12 : ℝ)) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X ^ (11 / 12 : ℝ) := by norm_num
  have hfirst :
      X *
          ((((⌈X⌉₊ ^ 2 : ℕ) : ℝ) ^ (-1 / 6 : ℝ)) +
            6 * (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ)) ≤
        7 * X ^ (11 / 12 : ℝ) := by
    calc
      X *
          ((((⌈X⌉₊ ^ 2 : ℕ) : ℝ) ^ (-1 / 6 : ℝ)) +
            6 * (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ)) ≤
          X *
            ((main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ) +
              6 * (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ)) := by
        gcongr
      _ = 7 *
          (X * (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ)) := by ring
      _ ≤ 7 * (X * X ^ (-1 / 12 : ℝ)) := by
        gcongr
      _ = 7 * X ^ (11 / 12 : ℝ) := by rw [hfirstPower]
  have hsecond :
      X ^ (5 / 6 : ℝ) *
          (2 + Real.log ((⌈X⌉₊ ^ 2 - 1 : ℕ) : ℝ)) ≤
        6 * X ^ (5 / 6 : ℝ) * Real.log X := by
    have hparenthesis :
        2 + Real.log ((⌈X⌉₊ ^ 2 - 1 : ℕ) : ℝ) ≤
          6 * Real.log X := by linarith
    calc
      X ^ (5 / 6 : ℝ) *
          (2 + Real.log ((⌈X⌉₊ ^ 2 - 1 : ℕ) : ℝ)) ≤
          X ^ (5 / 6 : ℝ) * (6 * Real.log X) :=
        mul_le_mul_of_nonneg_left hparenthesis
          (Real.rpow_nonneg hXpos.le _)
      _ = 6 * X ^ (5 / 6 : ℝ) * Real.log X := by ring
  calc
    main4FriedlanderIwaniecHighAbelRectangleScale X ≤
        128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (X *
              ((((⌈X⌉₊ ^ 2 : ℕ) : ℝ) ^ (-1 / 6 : ℝ)) +
                6 * (main4WilsonAbelSplitPoint X : ℝ) ^ (-1 / 6 : ℝ)) +
            X ^ (5 / 6 : ℝ) *
              (2 + Real.log ((⌈X⌉₊ ^ 2 - 1 : ℕ) : ℝ))) := hbase
    _ ≤ 128 * (Real.log X) ^ (7 / 6 : ℝ) *
          (7 * X ^ (11 / 12 : ℝ) +
            6 * X ^ (5 / 6 : ℝ) * Real.log X) := by
      gcongr
    _ = 896 * X ^ (11 / 12 : ℝ) *
          (Real.log X) ^ (7 / 6 : ℝ) +
        768 * X ^ (5 / 6 : ℝ) *
          (Real.log X) ^ (13 / 6 : ℝ) := by
      rw [show (Real.log X) ^ (13 / 6 : ℝ) =
          (Real.log X) ^ (7 / 6 : ℝ) * Real.log X by
        calc
          (Real.log X) ^ (13 / 6 : ℝ) =
              (Real.log X) ^ ((7 / 6 : ℝ) + 1) := by norm_num
          _ = (Real.log X) ^ (7 / 6 : ℝ) *
              (Real.log X) ^ (1 : ℝ) := Real.rpow_add
                (zero_lt_one.trans_le hlogOne) _ _
          _ = (Real.log X) ^ (7 / 6 : ℝ) * Real.log X := by
            rw [Real.rpow_one]]
      ring

/-! ## Final bridge from the two published inputs -/

/-- Wilson's weighted rectangle estimate and the Friedlander--Iwaniec
rectangle estimate together prove the exact away-from-eight finite moment
used by the rest of the Corollary 1.2 formalization. -/
theorem main4WilsonFinitePolynomialMomentAwayFromEight_of_rectangleEstimates
    (hWilson : Main4WilsonWeightedRectangleEstimate)
    (hFI : Main4FriedlanderIwaniecRectangleEstimate) :
    Main4WilsonFinitePolynomialMomentAwayFromEight := by
  obtain ⟨Cw, hCw, hWilsonBound⟩ := hWilson
  obtain ⟨Cf, hCf, hFIBound⟩ := hFI
  let K := main4WilsonLowShiftedSeriesConstant
  have hK : 0 ≤ K := main4WilsonLowShiftedSeriesConstant_nonneg
  let Cfinal := Cw * (16 * K + 256) + 1664 * Cf
  have hCfinal : 0 < Cfinal := by
    dsimp only [Cfinal]
    have hleft : 0 < Cw * (16 * K + 256) := by positivity
    have hright : 0 < 1664 * Cf := by positivity
    positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  filter_upwards [eventually_main4Wilson_error_one_le_naturalScale,
      eventually_main4Wilson_error_two_le_naturalScale,
      eventually_ge_atTop (64 : ℝ)] with X herrorOne herrorTwo hX
  have hXpos : 0 < X := by linarith
  have hlogPos : 0 < Real.log X := Real.log_pos (by linarith)
  let F := X / Real.sqrt (Real.log X)
  have hF : 0 ≤ F := by
    dsimp only [F]
    positivity
  have hfinite :=
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight_le_low_high_scales
      hWilsonBound hFIBound (by linarith : 16 ≤ X)
  have hlow := main4WilsonLowAbelRectangleScale_le_naturalScale_add_error hX
  have hhigh := main4FriedlanderIwaniecHighAbelRectangleScale_le_errors hX
  have hlowTarget :
      main4WilsonLowAbelRectangleScale X ≤ (16 * K + 256) * F := by
    calc
      main4WilsonLowAbelRectangleScale X ≤
          16 * K * F +
            256 * X ^ (11 / 12 : ℝ) *
              (Real.log X) ^ (7 / 6 : ℝ) := by
        simpa only [K, F] using hlow
      _ ≤ 16 * K * F + 256 * F := by
        have herr := mul_le_mul_of_nonneg_left herrorOne
          (by norm_num : (0 : ℝ) ≤ 256)
        nlinarith
      _ = (16 * K + 256) * F := by ring
  have hhighTarget :
      main4FriedlanderIwaniecHighAbelRectangleScale X ≤ 1664 * F := by
    calc
      main4FriedlanderIwaniecHighAbelRectangleScale X ≤
          896 * X ^ (11 / 12 : ℝ) *
              (Real.log X) ^ (7 / 6 : ℝ) +
            768 * X ^ (5 / 6 : ℝ) *
              (Real.log X) ^ (13 / 6 : ℝ) := hhigh
      _ ≤ 896 * F + 768 * F := by
        have herrOne := mul_le_mul_of_nonneg_left herrorOne
          (by norm_num : (0 : ℝ) ≤ 896)
        have herrTwo := mul_le_mul_of_nonneg_left herrorTwo
          (by norm_num : (0 : ℝ) ≤ 768)
        nlinarith
      _ = 1664 * F := by ring
  change main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X ≤
    Cfinal * F
  calc
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X ≤
        Cw * main4WilsonLowAbelRectangleScale X +
          Cf * main4FriedlanderIwaniecHighAbelRectangleScale X := hfinite
    _ ≤ Cw * ((16 * K + 256) * F) + Cf * (1664 * F) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlowTarget hCw.le)
        (mul_le_mul_of_nonneg_left hhighTarget hCf.le)
    _ = Cfinal * F := by
      dsimp only [Cfinal]
      ring

/-- Corollary 1.2, now conditional directly on the two published analytic
rectangle theorems and on no project-internal finite-moment placeholder. -/
theorem realQuadraticFieldOddClassAverageAssertion_of_rectangleEstimates
    (hWilson : Main4WilsonWeightedRectangleEstimate)
    (hFI : Main4FriedlanderIwaniecRectangleEstimate) :
    RealQuadraticFieldOddClassAverageAssertion :=
  realQuadraticFieldOddClassAverageAssertion_conditional_on_wilsonFinitePolynomialMomentAwayFromEight
    (main4WilsonFinitePolynomialMomentAwayFromEight_of_rectangleEstimates
      hWilson hFI)

end

end PellPaper
