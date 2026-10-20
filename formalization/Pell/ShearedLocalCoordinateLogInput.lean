import Pell.LocalLogarithmRateAbsorption
import Pell.ShearedExponentialEvaluationMatrixAlignment

/-!
# Feeding local factor coordinates into the sheared determinant input

The source-normalized determinant endpoint is indexed by an arbitrary finite
row type and asks for bounds on reindexed logarithmic coordinates.  This file
transports the concrete local-ratio bounds to that exact input shape.  All
localization intervals, factor conditions, scale relations, and exponential
slack remain pointwise hypotheses.
-/

namespace PellPaper

noncomputable section

/-- Pointwise source localizations give the first reindexed logarithmic input
for the sheared determinant estimate. -/
theorem generalBidegreeReindexedLogS_bound_of_localizedIntervals
    {ι : Type*} (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (s₀ M m L : ℝ) (d e : ι → ℕ)
    (hs₀ : 0 < s₀) (hM : 1 ≤ M)
    (hlower : ∀ row, s₀ ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row, (d row : ℝ) / (e row : ℝ) ≤ s₀ * (1 + 1 / M))
    (hdecay : m * L ≤ Real.log M) :
    ∀ r, |generalBidegreeReindexedLogS A B eRows
      (fun row => localSourceRatio s₀ (d row) (e row)) r| ≤
        Real.exp (-(m * L)) := by
  intro r
  simpa [generalBidegreeReindexedLogS] using
    (abs_log_localSourceRatio_le_exp_neg_of_log_scale hs₀ hM
      (hlower (eRows.symm r)) (hupper (eRows.symm r)) hdecay)

/-- Pointwise dyadic local data give the second reindexed logarithmic input
for the sheared determinant estimate, with the explicit slack needed to
absorb the fixed factor two in the local displacement estimate. -/
theorem generalBidegreeReindexedShearedLogT_bound_of_dyadicLocalScale
    {ι : Type*} (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    {θ : ℝ} {Y : ℕ} (s₀ X σ : ℝ)
    (d e u v : ι → ℕ)
    (hcond : ∀ row, DyadicFactorCondition θ Y (d row) (e row) (u row) (v row))
    (hs₀ : 0 < s₀) (hX : 2 ≤ X)
    (hS : ∀ row, 1 ≤ localSourceRatio s₀ (d row) (e row))
    (hscale : ∀ row,
      2 * X ≤ s₀ ^ 2 * (e row : ℝ) ^ 2 * (u row : ℝ))
    (hσ : 0 < σ) (hlarge : Real.exp (Real.log 2 / σ) ≤ X) :
    ∀ r, |generalBidegreeReindexedShearedLogT A B eRows
      (fun row => localSourceRatio s₀ (d row) (e row))
      (fun row => localTargetRatio s₀ (u row) (v row)) r| ≤
        Real.exp (-(1 - σ) * Real.log X) := by
  intro r
  simpa [generalBidegreeReindexedShearedLogT] using
    (dyadicFactorCondition_abs_sheared_log_localRatios_le_exp_neg_one_sub_slack_log
      (hcond (eRows.symm r)) hs₀ hX (hS (eRows.symm r))
      (hscale (eRows.symm r)) hσ hlarge)

end

end PellPaper
