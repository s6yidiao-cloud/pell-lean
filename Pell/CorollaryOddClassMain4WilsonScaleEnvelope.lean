import Pell.CorollaryOddClassMain4WilsonAbelSynthesis

/-!
# Common large-scale envelopes for the four Main4 rectangle branches

This module isolates the elementary ceiling, logarithm, and real-power
comparisons needed after the Wilson/Friedlander--Iwaniec rectangle inputs
have been specialized to the four exact branch cutoffs.  It contains no
analytic estimate: it only bounds the already defined source scales by
common pointwise envelopes when `64 ≤ X`.
-/

namespace PellPaper

noncomputable section

/-! ## Reusable ceiling geometry -/

/-- The outer ceiling lies between `X` and `2X` once `X ≥ 64`. -/
theorem main4Wilson_ceilX_bounds {X : ℝ} (hX : 64 ≤ X) :
    X ≤ (⌈X⌉₊ : ℝ) ∧ (⌈X⌉₊ : ℝ) ≤ 2 * X := by
  constructor
  · exact Nat.le_ceil X
  · have hlt : (⌈X⌉₊ : ℝ) < X + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    linarith

/-- The ceiling of `sqrt X` lies between `sqrt X` and `2 sqrt X`. -/
theorem main4Wilson_ceilSqrt_bounds {X : ℝ} (hX : 64 ≤ X) :
    Real.sqrt X ≤ (main4WilsonAbelSplitPoint X : ℝ) ∧
      (main4WilsonAbelSplitPoint X : ℝ) ≤ 2 * Real.sqrt X := by
  have hX0 : 0 ≤ X := by linarith
  have hsqrtOne : 1 ≤ Real.sqrt X := by
    nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
  unfold main4WilsonAbelSplitPoint
  constructor
  · exact Nat.le_ceil (Real.sqrt X)
  · have hlt : (⌈Real.sqrt X⌉₊ : ℝ) < Real.sqrt X + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg X)
    linarith

/-- The exact Abel endpoint `ceil(X)^2` lies in `[X^2,4X^2]`. -/
theorem main4Wilson_terminalEndpoint_bounds {X : ℝ} (hX : 64 ≤ X) :
    X ^ 2 ≤ ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) ∧
      ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) ≤ 4 * X ^ 2 := by
  obtain ⟨hYlo, hYhi⟩ := main4Wilson_ceilX_bounds hX
  have hX0 : 0 ≤ X := by linarith
  norm_num only [Nat.cast_pow]
  constructor
  · nlinarith
  · nlinarith

/-- Geometry shared by any branch scale between `X/8` and `2X`.
In particular it records the logarithmic lower bound needed to compare
the denominators in Wilson's scale. -/
theorem main4Wilson_branchScale_geometry
    {X : ℝ} {M : ℕ} (hX : 64 ≤ X)
    (hMlo : X / 8 ≤ (M : ℝ)) (hMhi : (M : ℝ) ≤ 2 * X) :
    0 < (M : ℝ) ∧ X / 8 ≤ (M : ℝ) ∧
      (M : ℝ) ≤ 2 * X ∧
        Real.log X / 2 ≤ Real.log (M : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hM8 : (8 : ℝ) ≤ (M : ℝ) := by linarith
  have hM0 : 0 < (M : ℝ) := by linarith
  have hXsquared : X ≤ (M : ℝ) ^ 2 := by
    nlinarith
  have hlog := Real.log_le_log hX0 hXsquared
  rw [Real.log_pow] at hlog
  norm_num at hlog
  exact ⟨hM0, hMlo, hMhi, by linarith⟩

/-- All three distinct branch ceilings satisfy the common scale geometry. -/
theorem main4Wilson_threeBranchCeil_geometry {X : ℝ} (hX : 64 ≤ X) :
    (X / 8 ≤ (⌈X⌉₊ : ℝ) ∧ (⌈X⌉₊ : ℝ) ≤ 2 * X) ∧
    (X / 8 ≤ (⌈X / 4⌉₊ : ℝ) ∧ (⌈X / 4⌉₊ : ℝ) ≤ 2 * X) ∧
    (X / 8 ≤ (⌈X / 8⌉₊ : ℝ) ∧ (⌈X / 8⌉₊ : ℝ) ≤ 2 * X) := by
  obtain ⟨hYlo, hYhi⟩ := main4Wilson_ceilX_bounds hX
  have hX0 : 0 ≤ X := by linarith
  have hQuarterCeil : (⌈X / 4⌉₊ : ℝ) < X / 4 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hEighthCeil : (⌈X / 8⌉₊ : ℝ) < X / 8 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  constructor
  · exact ⟨hXlo.trans hYlo, hYhi⟩
  constructor
  · exact ⟨by
      exact (show X / 8 ≤ X / 4 by linarith).trans (Nat.le_ceil (X / 4)), by
      linarith⟩
  · exact ⟨Nat.le_ceil (X / 8), by linarith⟩
  where
    hXlo : X / 8 ≤ X := by linarith

/-! ## Geometry at the low Abel split -/

theorem main4WilsonAbelSplitPoint_two_le_of_large
    {X : ℝ} (hX : 64 ≤ X) :
    2 ≤ main4WilsonAbelSplitPoint X :=
  main4WilsonAbelSplitPoint_two_le (by linarith)

/-- A convenient quarter-power bound for the shifted low endpoint. -/
theorem main4Wilson_sqrt_splitPoint_add_one_le
    {X : ℝ} (hX : 64 ≤ X) :
    Real.sqrt ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ) ≤
      2 * X ^ (1 / 4 : ℝ) := by
  have hX0 : 0 ≤ X := by linarith
  have hsqrtOne : 1 ≤ Real.sqrt X := by
    nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
  have hS := (main4Wilson_ceilSqrt_bounds hX).2
  have hinside :
      ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ) ≤
        4 * Real.sqrt X := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  calc
    Real.sqrt ((main4WilsonAbelSplitPoint X + 1 : ℕ) : ℝ) ≤
        Real.sqrt (4 * Real.sqrt X) :=
      Real.sqrt_le_sqrt hinside
    _ = 2 * Real.sqrt (Real.sqrt X) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ = 2 * X ^ (1 / 4 : ℝ) := by
      congr 1
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0]
      norm_num

/-- Prefixes below `ceil(sqrt X)` (including the `max 2` repair at one)
have logarithm at most `log X`. -/
theorem main4Wilson_log_max_two_le_logX_of_le_splitPoint
    {X : ℝ} {r : ℕ} (hX : 64 ≤ X)
    (hr : r ≤ main4WilsonAbelSplitPoint X) :
    Real.log ((max 2 r : ℕ) : ℝ) ≤ Real.log X := by
  have hX0 : 0 < X := by linarith
  have hS := (main4Wilson_ceilSqrt_bounds hX).2
  have hsqrt0 := Real.sqrt_nonneg X
  have hsqrtSq := Real.sq_sqrt (by linarith : 0 ≤ X)
  have htwo : (2 : ℝ) ≤ X := by linarith
  have hrReal : (r : ℝ) ≤ X := by
    have hrs : (r : ℝ) ≤ (main4WilsonAbelSplitPoint X : ℝ) := by
      exact_mod_cast hr
    have htwoSqrt : 2 * Real.sqrt X ≤ X := by nlinarith
    linarith
  have hmax : ((max 2 r : ℕ) : ℝ) ≤ X := by
    simp only [Nat.cast_max, Nat.cast_ofNat]
    exact max_le htwo hrReal
  exact Real.log_le_log (by positivity) hmax

/-! ## Pointwise Wilson envelope -/

/-- The common two-term Wilson expression before accounting for the four
branches. -/
def main4WilsonPointwiseEnvelope (X : ℝ) (r : ℕ) : ℝ :=
  X * Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
      Real.sqrt (Real.log X) +
    X ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
      Real.sqrt (Real.log (r : ℝ)) /
        (Real.log X) ^ (1 / 4 : ℝ)

/-- A single branch between `X/8` and `2X` costs at most four copies of
the common Wilson expression. -/
theorem main4WilsonWeightedRectangleScale_le_pointwiseEnvelope
    {X : ℝ} {M r : ℕ} (hX : 64 ≤ X)
    (hMlo : X / 8 ≤ (M : ℝ)) (hMhi : (M : ℝ) ≤ 2 * X)
    (hr : 2 ≤ r) :
    main4WilsonWeightedRectangleScale M r ≤
      4 * main4WilsonPointwiseEnvelope X r := by
  obtain ⟨hM0, _, _, hlogHalf⟩ :=
    main4Wilson_branchScale_geometry hX hMlo hMhi
  have hX0 : 0 < X := by linarith
  have hXone : 1 < X := by linarith
  have hMone : 1 < (M : ℝ) := by linarith
  have hrone : 1 < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hMone
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hrone
  have hsqrtLog :
      Real.sqrt (Real.log X) ≤
        2 * Real.sqrt (Real.log (M : ℝ)) := by
    have hxSq := Real.sq_sqrt hlogX.le
    have hmSq := Real.sq_sqrt hlogM.le
    nlinarith [Real.sqrt_nonneg (Real.log X),
      Real.sqrt_nonneg (Real.log (M : ℝ))]
  have hquarterLog :
      (Real.log X) ^ (1 / 4 : ℝ) ≤
        2 * (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) := by
    have hlogTwo : Real.log X ≤ 2 * Real.log (M : ℝ) := by linarith
    have htwoPow : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 4 : ℝ) ≤ 1))
    calc
      (Real.log X) ^ (1 / 4 : ℝ) ≤
          (2 * Real.log (M : ℝ)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hlogX.le hlogTwo (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) *
          (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlogM.le]
      _ ≤ 2 * (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hlogM.le _)
  have hMpow :
      (M : ℝ) ^ (2 / 3 : ℝ) ≤ 2 * X ^ (2 / 3 : ℝ) := by
    have htwoPow : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (2 / 3 : ℝ) ≤ 1))
    calc
      (M : ℝ) ^ (2 / 3 : ℝ) ≤
          (2 * X) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hMhi (by norm_num)
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * X ^ (2 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le]
      _ ≤ 2 * X ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hX0.le _)
  have htermOne :
      (M : ℝ) * Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
          Real.sqrt (Real.log (M : ℝ)) ≤
        4 * (X * Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
          Real.sqrt (Real.log X)) := by
    calc
      (M : ℝ) * Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
          Real.sqrt (Real.log (M : ℝ)) ≤
          (4 * (X * Real.sqrt (r : ℝ) * Real.log (r : ℝ))) /
            Real.sqrt (Real.log X) := by
        apply (div_le_div_iff₀ (Real.sqrt_pos.2 hlogM)
          (Real.sqrt_pos.2 hlogX)).2
        calc
          ((M : ℝ) * Real.sqrt (r : ℝ) * Real.log (r : ℝ)) *
              Real.sqrt (Real.log X) ≤
              ((2 * X) * Real.sqrt (r : ℝ) * Real.log (r : ℝ)) *
                (2 * Real.sqrt (Real.log (M : ℝ))) := by
            gcongr
          _ = (4 * (X * Real.sqrt (r : ℝ) * Real.log (r : ℝ))) *
              Real.sqrt (Real.log (M : ℝ)) := by ring
      _ = 4 * (X * Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
          Real.sqrt (Real.log X)) := by ring
  have htermTwo :
      (M : ℝ) ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
          Real.sqrt (Real.log (r : ℝ)) /
            (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) ≤
        4 * (X ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
          Real.sqrt (Real.log (r : ℝ)) /
            (Real.log X) ^ (1 / 4 : ℝ)) := by
    have hdenM : 0 < (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_pos_of_pos hlogM _
    have hdenX : 0 < (Real.log X) ^ (1 / 4 : ℝ) :=
      Real.rpow_pos_of_pos hlogX _
    calc
      (M : ℝ) ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
          Real.sqrt (Real.log (r : ℝ)) /
            (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) ≤
          (4 * (X ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
            Real.sqrt (Real.log (r : ℝ)))) /
              (Real.log X) ^ (1 / 4 : ℝ) := by
        apply (div_le_div_iff₀ hdenM hdenX).2
        calc
          ((M : ℝ) ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
              Real.sqrt (Real.log (r : ℝ))) *
                (Real.log X) ^ (1 / 4 : ℝ) ≤
              ((2 * X ^ (2 / 3 : ℝ)) * (r : ℝ) ^ (3 / 2 : ℝ) *
                Real.sqrt (Real.log (r : ℝ))) *
                  (2 * (Real.log (M : ℝ)) ^ (1 / 4 : ℝ)) := by
            gcongr
          _ = (4 * (X ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
              Real.sqrt (Real.log (r : ℝ)))) *
                (Real.log (M : ℝ)) ^ (1 / 4 : ℝ) := by ring
      _ = 4 * (X ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
          Real.sqrt (Real.log (r : ℝ)) /
            (Real.log X) ^ (1 / 4 : ℝ)) := by ring
  unfold main4WilsonWeightedRectangleScale main4WilsonPointwiseEnvelope
  linarith

/-- The four exact cutoffs cost at most sixteen copies of the common
Wilson expression.  The upper restriction on `r` is included in the API
used by the Abel sums, although Wilson's pointwise comparison only needs
`2 ≤ r`. -/
theorem main4WilsonFourTwistRectangleScale_le_pointwiseEnvelope
    {X : ℝ} {r : ℕ} (hX : 64 ≤ X) (hr : 2 ≤ r)
    (_hrTop : r ≤ ⌈X⌉₊ ^ 2) :
    main4WilsonFourTwistRectangleScale X r ≤
      16 * main4WilsonPointwiseEnvelope X r := by
  obtain ⟨hOne, hFour, hEight⟩ := main4Wilson_threeBranchCeil_geometry hX
  have h₁ := main4WilsonWeightedRectangleScale_le_pointwiseEnvelope
    hX hOne.1 hOne.2 hr
  have h₄ := main4WilsonWeightedRectangleScale_le_pointwiseEnvelope
    hX hFour.1 hFour.2 hr
  have h₈ := main4WilsonWeightedRectangleScale_le_pointwiseEnvelope
    hX hEight.1 hEight.2 hr
  unfold main4WilsonFourTwistRectangleScale
  linarith

/-! ## Pointwise Friedlander--Iwaniec envelope -/

/-- The logarithm in every admissible branch is in fact bounded by
`4 log X`; this strengthens the coarser `8 log X` geometry quoted in the
paper-level calculation. -/
theorem main4FriedlanderIwaniec_branch_log_le_four_logX
    {X : ℝ} {M r : ℕ} (hX : 64 ≤ X)
    (hMlo : X / 8 ≤ (M : ℝ)) (hMhi : (M : ℝ) ≤ 2 * X)
    (hr : 2 ≤ r) (hrTop : r ≤ ⌈X⌉₊ ^ 2) :
    Real.log (3 * (M : ℝ) * (r : ℝ)) ≤ 4 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hM0 : 0 < (M : ℝ) := by linarith
  have hr0 : 0 < (r : ℝ) := by positivity
  have hrCast : (r : ℝ) ≤ ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hrTop
  have hrReal : (r : ℝ) ≤ 4 * X ^ 2 :=
    hrCast.trans (main4Wilson_terminalEndpoint_bounds hX).2
  have harg : 3 * (M : ℝ) * (r : ℝ) ≤ X ^ 4 := by
    calc
      3 * (M : ℝ) * (r : ℝ) ≤ 3 * (2 * X) * (4 * X ^ 2) := by
        gcongr
      _ = 24 * X ^ 3 := by ring
      _ ≤ X * X ^ 3 := by
        gcongr
        linarith
      _ = X ^ 4 := by ring
  have hlog := Real.log_le_log (by positivity : 0 < 3 * (M : ℝ) * (r : ℝ)) harg
  rw [Real.log_pow] at hlog
  norm_num at hlog
  exact hlog

/-- The common Friedlander--Iwaniec expression before the factor for four
branches. -/
def main4FriedlanderIwaniecPointwiseEnvelope (X : ℝ) (r : ℕ) : ℝ :=
  (Real.log X) ^ (7 / 6 : ℝ) *
    (X * (r : ℝ) ^ (5 / 6 : ℝ) +
      X ^ (5 / 6 : ℝ) * (r : ℝ))

/-- A single admissible branch costs at most thirty-two copies of the
common Friedlander--Iwaniec expression. -/
theorem main4FriedlanderIwaniecRectangleScale_le_pointwiseEnvelope
    {X : ℝ} {M r : ℕ} (hX : 64 ≤ X)
    (hMlo : X / 8 ≤ (M : ℝ)) (hMhi : (M : ℝ) ≤ 2 * X)
    (hr : 2 ≤ r) (hrTop : r ≤ ⌈X⌉₊ ^ 2) :
    main4FriedlanderIwaniecRectangleScale M r ≤
      32 * main4FriedlanderIwaniecPointwiseEnvelope X r := by
  have hX0 : 0 < X := by linarith
  have hXone : 1 < X := by linarith
  have hM0 : 0 < (M : ℝ) := by linarith
  have hr0 : 0 < (r : ℝ) := by positivity
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hlogArg : 0 < Real.log (3 * (M : ℝ) * (r : ℝ)) := by
    apply Real.log_pos
    have hM8 : (8 : ℝ) ≤ (M : ℝ) := by linarith
    have hrTwo : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  have hlogArgUpper := main4FriedlanderIwaniec_branch_log_le_four_logX
    hX hMlo hMhi hr hrTop
  have hfourPow : (4 : ℝ) ^ (7 / 6 : ℝ) ≤ 16 := by
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (7 / 6 : ℝ) ≤ 2)
    norm_num at hp ⊢
    exact hp
  have hlogPow :
      (Real.log (3 * (M : ℝ) * (r : ℝ))) ^ (7 / 6 : ℝ) ≤
        16 * (Real.log X) ^ (7 / 6 : ℝ) := by
    calc
      (Real.log (3 * (M : ℝ) * (r : ℝ))) ^ (7 / 6 : ℝ) ≤
          (4 * Real.log X) ^ (7 / 6 : ℝ) :=
        Real.rpow_le_rpow hlogArg.le hlogArgUpper (by norm_num)
      _ = (4 : ℝ) ^ (7 / 6 : ℝ) *
          (Real.log X) ^ (7 / 6 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hlogX.le]
      _ ≤ 16 * (Real.log X) ^ (7 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_right hfourPow (Real.rpow_nonneg hlogX.le _)
  have hMpow :
      (M : ℝ) ^ (5 / 6 : ℝ) ≤ 2 * X ^ (5 / 6 : ℝ) := by
    have htwoPow : (2 : ℝ) ^ (5 / 6 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (5 / 6 : ℝ) ≤ 1))
    calc
      (M : ℝ) ^ (5 / 6 : ℝ) ≤ (2 * X) ^ (5 / 6 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hMhi (by norm_num)
      _ = (2 : ℝ) ^ (5 / 6 : ℝ) * X ^ (5 / 6 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le]
      _ ≤ 2 * X ^ (5 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hX0.le _)
  have hrCancel :
      (r : ℝ) * (r : ℝ) ^ (-1 / 6 : ℝ) =
        (r : ℝ) ^ (5 / 6 : ℝ) := by
    calc
      (r : ℝ) * (r : ℝ) ^ (-1 / 6 : ℝ) =
          (r : ℝ) ^ (1 : ℝ) * (r : ℝ) ^ (-1 / 6 : ℝ) := by
        rw [Real.rpow_one]
      _ = (r : ℝ) ^ ((1 : ℝ) + (-1 / 6 : ℝ)) :=
        (Real.rpow_add hr0 _ _).symm
      _ = (r : ℝ) ^ (5 / 6 : ℝ) := by norm_num
  have hMCancel :
      (M : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ) =
        (M : ℝ) ^ (5 / 6 : ℝ) := by
    calc
      (M : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ) =
          (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ) := by
        rw [Real.rpow_one]
      _ = (M : ℝ) ^ ((1 : ℝ) + (-1 / 6 : ℝ)) :=
        (Real.rpow_add hM0 _ _).symm
      _ = (M : ℝ) ^ (5 / 6 : ℝ) := by norm_num
  have hcoreEq :
      (M : ℝ) * (r : ℝ) *
          ((r : ℝ) ^ (-1 / 6 : ℝ) +
            (M : ℝ) ^ (-1 / 6 : ℝ)) =
        (M : ℝ) * (r : ℝ) ^ (5 / 6 : ℝ) +
          (M : ℝ) ^ (5 / 6 : ℝ) * (r : ℝ) := by
    calc
      (M : ℝ) * (r : ℝ) *
          ((r : ℝ) ^ (-1 / 6 : ℝ) +
            (M : ℝ) ^ (-1 / 6 : ℝ)) =
          (M : ℝ) * ((r : ℝ) * (r : ℝ) ^ (-1 / 6 : ℝ)) +
            ((M : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ)) * (r : ℝ) := by
        ring
      _ = (M : ℝ) * (r : ℝ) ^ (5 / 6 : ℝ) +
          (M : ℝ) ^ (5 / 6 : ℝ) * (r : ℝ) := by
        rw [hrCancel, hMCancel]
  have hcore :
      (M : ℝ) * (r : ℝ) *
          ((r : ℝ) ^ (-1 / 6 : ℝ) +
            (M : ℝ) ^ (-1 / 6 : ℝ)) ≤
        2 * (X * (r : ℝ) ^ (5 / 6 : ℝ) +
          X ^ (5 / 6 : ℝ) * (r : ℝ)) := by
    rw [hcoreEq]
    calc
      (M : ℝ) * (r : ℝ) ^ (5 / 6 : ℝ) +
          (M : ℝ) ^ (5 / 6 : ℝ) * (r : ℝ) ≤
          (2 * X) * (r : ℝ) ^ (5 / 6 : ℝ) +
            (2 * X ^ (5 / 6 : ℝ)) * (r : ℝ) := by
        gcongr
      _ = 2 * (X * (r : ℝ) ^ (5 / 6 : ℝ) +
          X ^ (5 / 6 : ℝ) * (r : ℝ)) := by ring
  unfold main4FriedlanderIwaniecRectangleScale
  calc
    (M : ℝ) * (r : ℝ) *
        ((r : ℝ) ^ (-1 / 6 : ℝ) + (M : ℝ) ^ (-1 / 6 : ℝ)) *
          (Real.log (3 * (M : ℝ) * (r : ℝ))) ^ (7 / 6 : ℝ) ≤
        (2 * (X * (r : ℝ) ^ (5 / 6 : ℝ) +
          X ^ (5 / 6 : ℝ) * (r : ℝ))) *
            (16 * (Real.log X) ^ (7 / 6 : ℝ)) := by
      exact mul_le_mul hcore hlogPow
        (Real.rpow_nonneg hlogArg.le _) (by positivity)
    _ = 32 * main4FriedlanderIwaniecPointwiseEnvelope X r := by
      unfold main4FriedlanderIwaniecPointwiseEnvelope
      ring

/-- Summing the four exact branch cutoffs gives the advertised constant
`128`. -/
theorem main4FriedlanderIwaniecFourTwistRectangleScale_le_pointwiseEnvelope
    {X : ℝ} {r : ℕ} (hX : 64 ≤ X) (hr : 2 ≤ r)
    (hrTop : r ≤ ⌈X⌉₊ ^ 2) :
    main4FriedlanderIwaniecFourTwistRectangleScale X r ≤
      128 * main4FriedlanderIwaniecPointwiseEnvelope X r := by
  obtain ⟨hOne, hFour, hEight⟩ := main4Wilson_threeBranchCeil_geometry hX
  have h₁ := main4FriedlanderIwaniecRectangleScale_le_pointwiseEnvelope
    hX hOne.1 hOne.2 hr hrTop
  have h₄ := main4FriedlanderIwaniecRectangleScale_le_pointwiseEnvelope
    hX hFour.1 hFour.2 hr hrTop
  have h₈ := main4FriedlanderIwaniecRectangleScale_le_pointwiseEnvelope
    hX hEight.1 hEight.2 hr hrTop
  unfold main4FriedlanderIwaniecFourTwistRectangleScale
  linarith

/-! ## Fully expanded interfaces for the Abel sum module -/

theorem main4WilsonFourTwistRectangleScale_le_explicit
    {X : ℝ} {r : ℕ} (hX : 64 ≤ X) (hr : 2 ≤ r)
    (hrTop : r ≤ ⌈X⌉₊ ^ 2) :
    main4WilsonFourTwistRectangleScale X r ≤
      16 *
        (X * Real.sqrt (r : ℝ) * Real.log (r : ℝ) /
            Real.sqrt (Real.log X) +
          X ^ (2 / 3 : ℝ) * (r : ℝ) ^ (3 / 2 : ℝ) *
            Real.sqrt (Real.log (r : ℝ)) /
              (Real.log X) ^ (1 / 4 : ℝ)) := by
  simpa only [main4WilsonPointwiseEnvelope] using
    main4WilsonFourTwistRectangleScale_le_pointwiseEnvelope hX hr hrTop

theorem main4FriedlanderIwaniecFourTwistRectangleScale_le_explicit
    {X : ℝ} {r : ℕ} (hX : 64 ≤ X) (hr : 2 ≤ r)
    (hrTop : r ≤ ⌈X⌉₊ ^ 2) :
    main4FriedlanderIwaniecFourTwistRectangleScale X r ≤
      128 * (Real.log X) ^ (7 / 6 : ℝ) *
        (X * (r : ℝ) ^ (5 / 6 : ℝ) +
          X ^ (5 / 6 : ℝ) * (r : ℝ)) := by
  have h :=
    main4FriedlanderIwaniecFourTwistRectangleScale_le_pointwiseEnvelope
      hX hr hrTop
  unfold main4FriedlanderIwaniecPointwiseEnvelope at h
  nlinarith

end

end PellPaper
