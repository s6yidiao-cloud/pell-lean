import Pell.ClassAverageLayerCake
import Pell.ExponentialIntegralBound

/-!
# The conditional analytic reduction for the class-number average

For a finite family of nonnegative weights, a first-moment bound and uniform
exponential bounds for the subfamilies with small normalized regulator imply
the class-sum estimate.  These analytic bounds are hypotheses of the theorem
below; no estimate for quadratic Dirichlet `L`-values is asserted here.
-/

namespace PellPaper

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The weighted strict-threshold counting kernel of any finite family is
interval integrable away from zero. -/
theorem intervalIntegrable_finite_threshold_weights {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (L r : ι → ℝ) {r₀ T : ℝ}
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) :
    IntervalIntegrable
      (fun θ : ℝ ↦ (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2)
      volume r₀ T := by
  have h : IntervalIntegrable
      (fun θ : ℝ ↦ ∑ i ∈ s, L i * (if r i < θ then 1 / θ ^ 2 else 0))
      volume r₀ T := by
    constructor
    · exact integrable_finsetSum s fun i _ ↦
        ((intervalIntegrable_threshold_inverse_square (r i) hr₀ hT).const_mul (L i)).1
    · exact integrable_finsetSum s fun i _ ↦
        ((intervalIntegrable_threshold_inverse_square (r i) hr₀ hT).const_mul (L i)).2
  convert h using 1
  ext θ
  rw [Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [div_eq_mul_inv]

/-- A uniform exponential estimate for the weighted exceptional subfamilies
bounds their layer-cake integral by an explicit multiple of
`X / sqrt (log X)`. -/
theorem finite_threshold_integral_le_of_exponential_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (L r : ι → ℝ) (B₁ r₀ T a X : ℝ)
    (hB₁ : 0 ≤ B₁) (hr₀ : 0 < r₀) (hT : r₀ ≤ T)
    (ha : 0 < a) (hX : 1 < X)
    (hcount : ∀ θ ∈ Icc r₀ T,
      (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) ≤
        B₁ * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) :
    (∫ θ in r₀..T, (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2) ≤
      B₁ * X * ((((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a) /
        Real.sqrt (Real.log X)) := by
  have hBX : 0 ≤ B₁ * X := mul_nonneg hB₁ (by linarith)
  calc
    _ ≤ ∫ θ in r₀..T,
        B₁ * X * (Real.exp (-a * Real.log X / (θ + 1) ^ 2) / θ ^ 2) := by
      apply intervalIntegral.integral_mono_on hT
        (intervalIntegrable_finite_threshold_weights s L r hr₀ hT)
      · convert (intervalIntegrable_exponential_kernel (a * Real.log X) hr₀ hT).const_mul
          (B₁ * X) using 1
        simp only [neg_mul]
      · intro θ hθ
        simpa only [mul_div_assoc] using
          div_le_div_of_nonneg_right (hcount θ hθ) (sq_nonneg θ)
    _ = B₁ * X *
        ∫ θ in r₀..T, Real.exp (-a * Real.log X / (θ + 1) ^ 2) / θ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exponential_log_kernel_integral_le hr₀ hT ha hX) hBX

/-- The finite analytic implication used for the class-number average.

The class-number formula contributes `hpoint`, the first moment contributes
`htotal`, and the exceptional-set and second-moment estimates contribute
`hcount`.  The upper regulator cutoff is free, so its eventual choice can be
made separately from this finite reduction. -/
theorem finite_sum_class_bound_of_exponential_weighted_count
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (A B₀ B₁ r₀ T a X : ℝ)
    (hA : 0 ≤ A) (_hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) (ha : 0 < a) (hX : 1 < X)
    (hpoint : ∀ i ∈ s, h i ≤ A * (L i / r i))
    (htotal : (∑ i ∈ s, L i) ≤ B₀ * X)
    (hcount : ∀ θ ∈ Icc r₀ T,
      (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) ≤
        B₁ * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) :
    (∑ i ∈ s, h i) ≤ A * X *
      (B₀ / T + B₁ * ((((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a) /
        Real.sqrt (Real.log X))) := by
  have hT0 : 0 < T := hr₀.trans_le hT
  calc
    _ ≤ A * ((∑ i ∈ s, L i) / T +
        ∫ θ in r₀..T, (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2) :=
      finite_sum_class_bound_layer_cake s h L r A r₀ T hA hL hr hr₀ hT hpoint
    _ ≤ A * (B₀ * X / T + B₁ * X *
        ((((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a) / Real.sqrt (Real.log X))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add (div_le_div_of_nonneg_right htotal hT0.le)
        (finite_threshold_integral_le_of_exponential_bound s L r B₁ r₀ T a X
          hB₁ hr₀ hT ha hX hcount)
    _ = _ := by ring

end

end PellPaper
