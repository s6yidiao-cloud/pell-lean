import Pell.LocalLogarithmBounds

/-!
# Quantitative local displacement from explicit scale hypotheses

`LocalRatioIdentity` gives the exact local displacement
`h / (s₀² e² u)`.  This module records the elementary denominator comparison
needed to make that expression at most `X⁻¹`.  The required scale comparison
is an explicit hypothesis; `DyadicFactorCondition` supplies positivity and
the fact that the signed difference has absolute value at most two, but does
not itself contain the local box scales needed to prove that comparison.
-/

namespace PellPaper

/-- A signed numerator of absolute value at most two is at most `X⁻¹` after
division by a positive denominator that is at least `2X`. -/
theorem abs_div_le_one_div_of_abs_le_two_of_two_mul_le_denominator
    {h s₀ e u X : ℝ} (hs₀ : 0 < s₀) (he : 0 < e) (hu : 0 < u)
    (hX : 0 < X) (hh : |h| ≤ 2)
    (hscale : 2 * X ≤ s₀ ^ 2 * e ^ 2 * u) :
    |h / (s₀ ^ 2 * e ^ 2 * u)| ≤ 1 / X := by
  have hden_pos : 0 < s₀ ^ 2 * e ^ 2 * u :=
    mul_pos (mul_pos (sq_pos_of_pos hs₀) (sq_pos_of_pos he)) hu
  rw [abs_div, abs_of_pos hden_pos]
  calc
    |h| / (s₀ ^ 2 * e ^ 2 * u) ≤ 2 / (s₀ ^ 2 * e ^ 2 * u) :=
      div_le_div_of_nonneg_right hh hden_pos.le
    _ ≤ 1 / X := by
      apply (div_le_div_iff₀ hden_pos hX).mpr
      simpa using hscale

/-- A transparent lower-scale certificate for the denominator comparison.
For a source dyadic box one may take the three lower scales to be lower
bounds for the centre, `e`, and `u`, respectively. -/
theorem two_mul_le_local_displacement_denominator_of_lower_scales
    {s₀ e u X sₗ eₗ uₗ : ℝ}
    (hsₗ_pos : 0 < sₗ) (heₗ_pos : 0 < eₗ) (huₗ_pos : 0 < uₗ)
    (hsₗ : sₗ ≤ s₀) (heₗ : eₗ ≤ e) (huₗ : uₗ ≤ u)
    (hscale : 2 * X ≤ sₗ ^ 2 * eₗ ^ 2 * uₗ) :
    2 * X ≤ s₀ ^ 2 * e ^ 2 * u := by
  have hs_sq : sₗ ^ 2 ≤ s₀ ^ 2 :=
    pow_le_pow_left₀ hsₗ_pos.le hsₗ 2
  have he_sq : eₗ ^ 2 ≤ e ^ 2 :=
    pow_le_pow_left₀ heₗ_pos.le heₗ 2
  have hfirst : sₗ ^ 2 * eₗ ^ 2 ≤ s₀ ^ 2 * e ^ 2 :=
    mul_le_mul hs_sq he_sq (sq_nonneg eₗ) (sq_nonneg s₀)
  have hproduct : (sₗ ^ 2 * eₗ ^ 2) * uₗ ≤ (s₀ ^ 2 * e ^ 2) * u :=
    mul_le_mul hfirst huₗ huₗ_pos.le
      (mul_nonneg (sq_nonneg s₀) (sq_nonneg e))
  calc
    2 * X ≤ sₗ ^ 2 * eₗ ^ 2 * uₗ := hscale
    _ = (sₗ ^ 2 * eₗ ^ 2) * uₗ := by ring
    _ ≤ (s₀ ^ 2 * e ^ 2) * u := hproduct
    _ = s₀ ^ 2 * e ^ 2 * u := by ring

/-- The exact Pell local-ratio displacement is `O(X⁻¹)` once its full
denominator is at least `2X`.  All scale information is deliberately a
hypothesis rather than inferred from the factor equation. -/
theorem local_ratio_parabola_deviation_abs_le_one_div_of_scale
    {d e u v : ℕ} {h : ℤ} {s₀ X : ℝ}
    (hs₀ : 0 < s₀) (he : 0 < e) (hu : 0 < u)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h)
    (hX : 0 < X) (hh : |(h : ℝ)| ≤ 2)
    (hscale : 2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ)) :
    |localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2| ≤ 1 / X := by
  rw [local_ratio_parabola_identity hs₀.ne' he hu hdiff]
  exact abs_div_le_one_div_of_abs_le_two_of_two_mul_le_denominator
    hs₀ (by exact_mod_cast he) (by exact_mod_cast hu) hX hh hscale

/-- `DyadicFactorCondition` supplies the bounded numerator in the preceding
local scale lemma.  It does not supply `hscale`: that is exactly the missing
box-scale relation between `s₀`, `e`, `u`, and the source scale `X`. -/
theorem dyadicFactorCondition_local_ratio_parabola_deviation_abs_le_one_div_of_scale
    {θ : ℝ} {Y d e u v : ℕ} {s₀ X : ℝ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hs₀ : 0 < s₀) (hX : 0 < X)
    (hscale : 2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ)) :
    |localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2| ≤ 1 / X := by
  obtain ⟨h, hh, hdiff⟩ := dyadicFactorCondition_exists_difference hcond
  have he : 0 < e := hcond.2.1
  have hu : 0 < u := hcond.2.2.1
  have habs : |(h : ℝ)| ≤ 2 := by
    rcases hh with rfl | rfl | rfl | rfl <;> norm_num
  exact local_ratio_parabola_deviation_abs_le_one_div_of_scale
    hs₀ he hu hdiff hX habs hscale

/-- Lower bounds from a chosen dyadic box are enough to establish the
otherwise explicit `hscale` premise of the dyadic local-displacement bound. -/
theorem dyadicFactorCondition_local_ratio_parabola_deviation_abs_le_one_div_of_lower_scales
    {θ : ℝ} {Y d e u v : ℕ} {s₀ X sₗ eₗ uₗ : ℝ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hs₀ : 0 < s₀) (hX : 0 < X)
    (hsₗ_pos : 0 < sₗ) (heₗ_pos : 0 < eₗ) (huₗ_pos : 0 < uₗ)
    (hsₗ : sₗ ≤ s₀) (heₗ : eₗ ≤ (e : ℝ)) (huₗ : uₗ ≤ (u : ℝ))
    (hscale : 2 * X ≤ sₗ ^ 2 * eₗ ^ 2 * uₗ) :
    |localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2| ≤ 1 / X := by
  apply dyadicFactorCondition_local_ratio_parabola_deviation_abs_le_one_div_of_scale
    hcond hs₀ hX
  exact two_mul_le_local_displacement_denominator_of_lower_scales
    hsₗ_pos heₗ_pos huₗ_pos hsₗ heₗ huₗ hscale

/-- With the local source coordinate at least one, the explicit dyadic
scale inequality feeds directly into the sheared logarithm bound used by
the determinant argument. -/
theorem dyadicFactorCondition_abs_sheared_log_localRatios_le_two_div_of_scale
    {θ : ℝ} {Y d e u v : ℕ} {s₀ X : ℝ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hs₀ : 0 < s₀) (hX : 2 ≤ X)
    (hS : 1 ≤ localSourceRatio s₀ d e)
    (hscale : 2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ)) :
    |Real.log (localTargetRatio s₀ u v) -
        2 * Real.log (localSourceRatio s₀ d e)| ≤ 2 / X := by
  apply abs_sheared_log_localRatios_le_two_div_of_unit_additive_error hX hS
  exact dyadicFactorCondition_local_ratio_parabola_deviation_abs_le_one_div_of_scale
    hcond hs₀ (by linarith) hscale

end PellPaper
