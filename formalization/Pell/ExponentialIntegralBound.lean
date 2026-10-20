import Pell.ClassAverageLayerCake
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# Decay of the regulator layer-cake integral

The integral in the final class-number-average argument is bounded by splitting
at the square root of the exponential parameter.  The proof uses only two
pointwise majorants, a constant and the reciprocal square, and yields an explicit
constant depending on the fixed positive lower endpoint.
-/

namespace PellPaper

open MeasureTheory Set
open scoped Interval

noncomputable section

/-- Exponential decay is bounded by the reciprocal of its positive argument. -/
theorem exp_neg_le_one_div {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) ≤ 1 / u := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le hu
  linarith [Real.add_one_le_exp u]

/-- Uniform control of the shift in the denominator away from zero. -/
theorem shifted_square_le {r₀ θ : ℝ} (hr₀ : 0 < r₀) (hθ : r₀ ≤ θ) :
    (θ + 1) ^ 2 ≤ (1 + 1 / r₀) ^ 2 * θ ^ 2 := by
  have hθ0 : 0 < θ := hr₀.trans_le hθ
  have hc : 0 ≤ 1 + 1 / r₀ := by positivity
  have hratio : 1 ≤ θ / r₀ := (le_div_iff₀ hr₀).mpr (by simpa using hθ)
  simp only [div_eq_mul_inv] at hratio
  have hshift : θ + 1 ≤ (1 + 1 / r₀) * θ := by
    calc
      θ + 1 ≤ θ + θ * r₀⁻¹ := by
        simpa only [add_comm] using add_le_add_left hratio θ
      _ = _ := by simp only [div_eq_mul_inv]; ring
  nlinarith [sq_nonneg ((1 + 1 / r₀) * θ - (θ + 1))]

/-- The exponentially damped reciprocal square is bounded by a constant of
size `1 / b`, uniformly above the fixed positive lower endpoint. -/
theorem exponential_kernel_le_constant {r₀ θ b : ℝ}
    (hr₀ : 0 < r₀) (hθ : r₀ ≤ θ) (hb : 0 < b) :
    Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2 ≤ (1 + 1 / r₀) ^ 2 / b := by
  have hθ0 : 0 < θ := hr₀.trans_le hθ
  have hs : 0 < (θ + 1) ^ 2 := sq_pos_of_pos (by linarith)
  have ht : 0 < θ ^ 2 := sq_pos_of_pos hθ0
  calc
    Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2 ≤
        (1 / (b / (θ + 1) ^ 2)) / θ ^ 2 := by
      apply div_le_div_of_nonneg_right _ ht.le
      simpa only [neg_div] using exp_neg_le_one_div (div_pos hb hs)
    _ = (θ + 1) ^ 2 / (b * θ ^ 2) := by field_simp
    _ ≤ (1 + 1 / r₀) ^ 2 / b := by
      apply (div_le_div_iff₀ (mul_pos hb ht) hb).mpr
      nlinarith [shifted_square_le hr₀ hθ]

/-- The same kernel is always at most its undamped reciprocal square. -/
theorem exponential_kernel_le_inverse_square {θ b : ℝ} (hb : 0 ≤ b) :
    Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2 ≤ 1 / θ ^ 2 := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg θ)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _)

/-- Continuity supplies all integrability hypotheses for the damped kernel. -/
theorem intervalIntegrable_exponential_kernel {r₀ T : ℝ} (b : ℝ)
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) :
    IntervalIntegrable (fun θ : ℝ ↦ Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2)
      volume r₀ T := by
  apply ContinuousOn.intervalIntegrable_of_Icc hT
  apply ContinuousOn.div
  · apply ContinuousOn.rexp
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro θ hθ
      have : 0 < θ := hr₀.trans_le hθ.1
      positivity
  · fun_prop
  · intro θ hθ
    have : 0 < θ := hr₀.trans_le hθ.1
    positivity

/-- Integrating the constant majorant on any subinterval above `r₀`. -/
theorem exponential_kernel_integral_le_linear {r₀ u v b : ℝ}
    (hr₀ : 0 < r₀) (hu : r₀ ≤ u) (huv : u ≤ v) (hb : 0 < b) :
    (∫ θ in u..v, Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2) ≤
      (v - u) * ((1 + 1 / r₀) ^ 2 / b) := by
  calc
    _ ≤ ∫ _ in u..v, (1 + 1 / r₀) ^ 2 / b := by
      apply intervalIntegral.integral_mono_on huv
        (intervalIntegrable_exponential_kernel b (hr₀.trans_le hu) huv)
        intervalIntegrable_const
      intro θ hθ
      exact exponential_kernel_le_constant hr₀ (hu.trans hθ.1) hb
    _ = _ := by simp [mul_div_assoc]

/-- Integrating the reciprocal-square majorant on any positive interval. -/
theorem exponential_kernel_integral_le_reciprocal {u v b : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hb : 0 ≤ b) :
    (∫ θ in u..v, Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2) ≤ 1 / u - 1 / v := by
  calc
    _ ≤ ∫ θ in u..v, 1 / θ ^ 2 := by
      apply intervalIntegral.integral_mono_on huv
        (intervalIntegrable_exponential_kernel b hu huv)
      · apply ContinuousOn.intervalIntegrable_of_Icc huv
        apply ContinuousOn.div continuousOn_const
        · fun_prop
        · intro θ hθ
          have : 0 < θ := hu.trans_le hθ.1
          positivity
      · intro θ _
        exact exponential_kernel_le_inverse_square hb
    _ = _ := inverse_square_interval_integral hu (hu.trans_le huv)

/-- A free splitting point gives a bound independent of the upper endpoint. -/
theorem exponential_kernel_integral_le_split {r₀ T b U : ℝ}
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) (hb : 0 < b) (hU : 0 < U) :
    (∫ θ in r₀..T, Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2) ≤
      U * ((1 + 1 / r₀) ^ 2 / b) + 1 / U := by
  have hc : 0 ≤ (1 + 1 / r₀) ^ 2 / b := by positivity
  have hT0 : 0 < T := hr₀.trans_le hT
  by_cases hUr : U ≤ r₀
  · calc
      _ ≤ 1 / r₀ - 1 / T :=
        exponential_kernel_integral_le_reciprocal hr₀ hT hb.le
      _ ≤ 1 / r₀ := sub_le_self _ (by positivity)
      _ ≤ 1 / U := one_div_le_one_div_of_le hU hUr
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hU.le hc)
  · have hrU : r₀ ≤ U := le_of_lt (lt_of_not_ge hUr)
    by_cases hTU : T ≤ U
    · calc
        _ ≤ (T - r₀) * ((1 + 1 / r₀) ^ 2 / b) :=
          exponential_kernel_integral_le_linear hr₀ le_rfl hT hb
        _ ≤ U * ((1 + 1 / r₀) ^ 2 / b) := by
          apply mul_le_mul_of_nonneg_right _ hc
          linarith
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hUT : U ≤ T := le_of_lt (lt_of_not_ge hTU)
      calc
        _ = (∫ θ in r₀..U, Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2) +
            ∫ θ in U..T, Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2 := by
          exact (intervalIntegral.integral_add_adjacent_intervals
            (intervalIntegrable_exponential_kernel b hr₀ hrU)
            (intervalIntegrable_exponential_kernel b hU hUT)).symm
        _ ≤ (U - r₀) * ((1 + 1 / r₀) ^ 2 / b) + (1 / U - 1 / T) :=
          add_le_add (exponential_kernel_integral_le_linear hr₀ le_rfl hrU hb)
            (exponential_kernel_integral_le_reciprocal hU hUT hb.le)
        _ ≤ _ := by nlinarith [mul_nonneg hr₀.le hc, one_div_pos.mpr hT0]

/-- The integral has square-root decay in its exponential parameter, with an
explicit constant and no restriction on the upper endpoint. -/
theorem exponential_kernel_integral_le_sqrt {r₀ T b : ℝ}
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) (hb : 0 < b) :
    (∫ θ in r₀..T, Real.exp (-b / (θ + 1) ^ 2) / θ ^ 2) ≤
      ((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt b := by
  apply (exponential_kernel_integral_le_split hr₀ hT hb (Real.sqrt_pos.mpr hb)).trans_eq
  have hs : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hs2 := Real.sq_sqrt hb.le
  field_simp
  nlinarith

/-- The form used in the class-number-average proof: the decay is
`1 / sqrt (log X)`, uniformly in the upper integration cutoff. -/
theorem exponential_log_kernel_integral_le {r₀ T a X : ℝ}
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) (ha : 0 < a) (hX : 1 < X) :
    (∫ θ in r₀..T, Real.exp (-a * Real.log X / (θ + 1) ^ 2) / θ ^ 2) ≤
      (((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a) / Real.sqrt (Real.log X) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have h := exponential_kernel_integral_le_sqrt hr₀ hT (mul_pos ha hlog)
  simpa only [neg_mul, Real.sqrt_mul ha.le, div_mul_eq_div_div] using h

/-- The asymptotic estimate, allowing the upper endpoint to depend arbitrarily
on `X` as long as it eventually lies above the fixed lower endpoint. -/
theorem exponential_log_kernel_integral_isBigO {r₀ a : ℝ} (T : ℝ → ℝ)
    (hr₀ : 0 < r₀) (ha : 0 < a)
    (hT : ∀ᶠ X in Filter.atTop, r₀ ≤ T X) :
    Asymptotics.IsBigO Filter.atTop
      (fun X ↦ ∫ θ in r₀..T X, Real.exp (-a * Real.log X / (θ + 1) ^ 2) / θ ^ 2)
      (fun X ↦ 1 / Real.sqrt (Real.log X)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a, ?_⟩
  filter_upwards [hT, Filter.eventually_gt_atTop (1 : ℝ)] with X hTX hX
  have hnonneg : 0 ≤
      ∫ θ in r₀..T X, Real.exp (-a * Real.log X / (θ + 1) ^ 2) / θ ^ 2 := by
    apply intervalIntegral.integral_nonneg hTX
    intro θ _
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (Real.log X)), mul_one_div]
  exact exponential_log_kernel_integral_le hr₀ hTX ha hX

end

end PellPaper
