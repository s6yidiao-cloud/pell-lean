import Pell.LocalRatioDisplacementScale

/-!
# Absorbing the fixed local-logarithm constant into exponential slack

The determinant endpoint measures a local logarithmic coordinate on an
exponential scale.  The elementary local calculation gives `2 / X`; this
file records the exact large-scale conversion to
`exp (-(1 - σ) log X)`.  The loss `σ` and its explicit threshold are kept in
the statement, so this does not supply a source choice of determinant
parameters or a dyadic box-scale relation.
-/

namespace PellPaper

/-- A positive reciprocal is its exact exponential logarithmic form. -/
theorem one_div_eq_exp_neg_log {M : ℝ} (hM : 0 < M) :
    1 / M = Real.exp (-Real.log M) := by
  rw [Real.exp_neg, Real.exp_log hM]
  simp

/-- The localized source-coordinate logarithm is in the exponential form
used by a determinant estimate whenever the designated decay exponent is at
most `log M`. -/
theorem abs_log_localSourceRatio_le_exp_neg_of_log_scale
    {s₀ M m L : ℝ} {d e : ℕ}
    (hs₀ : 0 < s₀) (hM : 1 ≤ M)
    (hlower : s₀ ≤ (d : ℝ) / (e : ℝ))
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M))
    (hdecay : m * L ≤ Real.log M) :
    |Real.log (localSourceRatio s₀ d e)| ≤ Real.exp (-(m * L)) := by
  calc
    |Real.log (localSourceRatio s₀ d e)| ≤ 1 / M :=
      abs_log_localSourceRatio_le_one_div_of_localized_interval hs₀ hM hlower hupper
    _ = Real.exp (-Real.log M) := one_div_eq_exp_neg_log (by linarith)
    _ ≤ Real.exp (-(m * L)) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- The fixed factor two in a local `X⁻¹` bound is absorbed into any positive
exponential slack once `X ≥ exp(log 2 / σ)`. -/
theorem two_div_le_exp_neg_one_sub_slack_log
    {X σ : ℝ} (hσ : 0 < σ)
    (hlarge : Real.exp (Real.log 2 / σ) ≤ X) :
    2 / X ≤ Real.exp (-(1 - σ) * Real.log X) := by
  have hX : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hlarge
  have hlogquot : Real.log 2 / σ ≤ Real.log X := by
    apply (Real.exp_le_exp).mp
    simpa only [Real.exp_log hX] using hlarge
  have hlog : Real.log 2 ≤ σ * Real.log X := by
    have := (div_le_iff₀ hσ).mp hlogquot
    linarith
  calc
    2 / X = Real.exp (Real.log 2 - Real.log X) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hX]
    _ ≤ Real.exp (-(1 - σ) * Real.log X) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- A dyadic factor tuple satisfying the explicit local scale condition has
the sheared logarithm bound in the exponential form consumed by determinant
arguments, after a declared fixed slack. -/
theorem dyadicFactorCondition_abs_sheared_log_localRatios_le_exp_neg_one_sub_slack_log
    {θ : ℝ} {Y d e u v : ℕ} {s₀ X σ : ℝ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hs₀ : 0 < s₀) (hX : 2 ≤ X)
    (hS : 1 ≤ localSourceRatio s₀ d e)
    (hscale : 2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ))
    (hσ : 0 < σ) (hlarge : Real.exp (Real.log 2 / σ) ≤ X) :
    |Real.log (localTargetRatio s₀ u v) -
        2 * Real.log (localSourceRatio s₀ d e)| ≤
      Real.exp (-(1 - σ) * Real.log X) := by
  exact (dyadicFactorCondition_abs_sheared_log_localRatios_le_two_div_of_scale
    hcond hs₀ hX hS hscale).trans
      (two_div_le_exp_neg_one_sub_slack_log hσ hlarge)

end PellPaper
