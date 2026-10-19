import Pell.ClassAverageAnalyticReduction
import Pell.ClassAverageCutoff

/-!
# The final scale in the conditional class-average argument

At the cutoff `c * sqrt (log X / log (log X))`, the reciprocal-square-root
logarithm term from the exponential integral is no larger than the cutoff
term, once `X ≥ exp (exp 1)`.  This module turns the conditional finite
analytic estimate into the scale appearing in the class-average target.
The first moment, weighted exceptional estimate, and class-number formula
remain explicit hypotheses.
-/

namespace PellPaper

open Set
open scoped BigOperators

noncomputable section

/-- An explicit range in which both logarithms have the required size. -/
theorem classAverage_large_log_bounds {X : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) :
    Real.exp 1 < X ∧ 1 ≤ Real.log (Real.log X) := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hex : Real.exp 1 < X := (Real.exp_lt_exp.mpr he).trans_le hX
  have hpos : 0 < X := (Real.exp_pos 1).trans hex
  have hlog : Real.exp 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hpos).mpr hX
  exact ⟨hex, (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hlog)).mpr hlog⟩

/-- The exponential-integral saving is at least as strong as the
reciprocal-cutoff saving in the explicit large-`X` range. -/
theorem one_div_sqrt_log_le_classAverage_saving {X : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) :
    1 / Real.sqrt (Real.log X) ≤
      Real.sqrt (Real.log (Real.log X) / Real.log X) := by
  have hb := classAverage_large_log_bounds hX
  rw [Real.sqrt_div' _ (classAverageCutoff_log_pos hb.1).le]
  exact div_le_div_of_nonneg_right (Real.one_le_sqrt.mpr hb.2)
    (Real.sqrt_nonneg _)

/-- An equivalent direct comparison with the reciprocal cutoff. -/
theorem one_div_sqrt_log_le_c_div_classAverageCutoff {c X : ℝ}
    (hc : 0 < c) (hX : Real.exp (Real.exp 1) ≤ X) :
    1 / Real.sqrt (Real.log X) ≤ c / classAverageCutoff c X := by
  calc
    _ ≤ Real.sqrt (Real.log (Real.log X) / Real.log X) :=
      one_div_sqrt_log_le_classAverage_saving hX
    _ = c / classAverageCutoff c X := by
      symm
      calc
        _ = c * (1 / classAverageCutoff c X) := div_eq_mul_one_div _ _
        _ = c * ((1 / c) *
            Real.sqrt (Real.log (Real.log X) / Real.log X)) := by
          rw [one_div_classAverageCutoff]
        _ = _ := by simp [hc.ne']

/-- The elementary final-scale comparison, with the integral constant kept
as an arbitrary nonnegative number `K`. -/
theorem classAverage_final_scale_bound {B₀ B₁ K c X : ℝ}
    (hB₁ : 0 ≤ B₁) (hK : 0 ≤ K)
    (hX : Real.exp (Real.exp 1) ≤ X) :
    (Real.sqrt X / Real.log X) * X *
        (B₀ / classAverageCutoff c X + B₁ * (K / Real.sqrt (Real.log X))) ≤
      (B₀ / c + B₁ * K) * classAverageScale X := by
  have hex := (classAverage_large_log_bounds hX).1
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hex
  have hXpos : 0 < X := zero_lt_one.trans hXone
  have hbase : 0 ≤ Real.rpow X (3 / 2) / Real.log X :=
    div_nonneg (Real.rpow_nonneg hXpos.le _) (Real.log_pos hXone).le
  have hsave :
      (Real.rpow X (3 / 2) / Real.log X) * (1 / Real.sqrt (Real.log X)) ≤
        classAverageScale X := by
    rw [classAverageScale_eq_base_mul_saving hXone]
    exact mul_le_mul_of_nonneg_left
      (one_div_sqrt_log_le_classAverage_saving hX) hbase
  have hfirst :
      ((Real.rpow X (3 / 2) / Real.log X) * B₀) / classAverageCutoff c X =
        (B₀ / c) * classAverageScale X := by
    calc
      _ = B₀ * ((Real.rpow X (3 / 2) / Real.log X) /
          classAverageCutoff c X) := by ring
      _ = _ := by rw [base_div_classAverageCutoff hXone]; ring
  calc
    _ = ((Real.rpow X (3 / 2) / Real.log X) * B₀) / classAverageCutoff c X +
        (B₁ * K) * ((Real.rpow X (3 / 2) / Real.log X) *
          (1 / Real.sqrt (Real.log X))) := by
      rw [rpow_three_halves_eq_mul_sqrt hXpos]
      ring
    _ ≤ (B₀ / c) * classAverageScale X + (B₁ * K) * classAverageScale X := by
      rw [hfirst]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hsave (mul_nonneg hB₁ hK))
    _ = _ := by ring

/-- The conditional finite class-average bound at the manuscript's cutoff.

The hypotheses include the class-number-formula pointwise bound, the first
moment, and the exponential weighted exceptional-set estimate.  Supplying
these arithmetic and analytic estimates is separate from this corollary. -/
theorem finite_sum_class_bound_at_classAverageCutoff
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (B₀ B₁ r₀ a c X : ℝ)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (_hc : 0 < c) (ha : 0 < a)
    (hX : Real.exp (Real.exp 1) ≤ X)
    (hT : r₀ ≤ classAverageCutoff c X)
    (hpoint : ∀ i ∈ s,
      h i ≤ (Real.sqrt X / Real.log X) * (L i / r i))
    (htotal : (∑ i ∈ s, L i) ≤ B₀ * X)
    (hcount : ∀ θ ∈ Icc r₀ (classAverageCutoff c X),
      (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) ≤
        B₁ * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) :
    (∑ i ∈ s, h i) ≤
      (B₀ / c + B₁ * (((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a)) *
        classAverageScale X := by
  have hex := (classAverage_large_log_bounds hX).1
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hex
  have hA : 0 ≤ Real.sqrt X / Real.log X :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_pos hXone).le
  have hK : 0 ≤ ((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a := by positivity
  exact (finite_sum_class_bound_of_exponential_weighted_count
    s h L r (Real.sqrt X / Real.log X) B₀ B₁ r₀
    (classAverageCutoff c X) a X hA hB₀ hB₁ hL hr hr₀ hT ha hXone
    hpoint htotal hcount).trans (classAverage_final_scale_bound hB₁ hK hX)

end

end PellPaper
