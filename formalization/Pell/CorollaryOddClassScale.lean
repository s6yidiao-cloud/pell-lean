import Pell.RealQuadraticFieldOddClassSum
import Pell.ClassAverageFinalReduction

/-!
# Elementary scale algebra for Corollary 1.2

The high-regulator term contains both the reciprocal moving cutoff and the
extra `1 / sqrt (log X)` from the genus-weighted first moment.  This file
identifies that expression with the exact scale of Corollary 1.2.  It also
absorbs the stronger `X^(3/2) / (log X)^3` low-regulator estimate.
-/

namespace PellPaper

noncomputable section

/-- The odd-class scale is the usual class-average base, times the moving
cutoff saving, and divided by one additional square root of the logarithm. -/
theorem oddClassAverageScale_eq_base_mul_saving_div_sqrt {X : ℝ}
    (hX : Real.exp 1 < X) :
    oddClassAverageScale X =
      (Real.rpow X (3 / 2) / Real.log X) *
        Real.sqrt (Real.log (Real.log X) / Real.log X) /
          Real.sqrt (Real.log X) := by
  have hlog : 0 < Real.log X := classAverageCutoff_log_pos hX
  rw [oddClassAverageScale, Real.sqrt_div' _ hlog.le,
    div_eq_mul_inv]
  have hsqrt : Real.sqrt (Real.log X) ≠ 0 :=
    (Real.sqrt_pos.2 hlog).ne'
  field_simp [hlog.ne', hsqrt]
  rw [Real.sq_sqrt hlog.le]

/-- At the moving cutoff, the high-regulator analytic expression is exactly
the target scale, up to the fixed reciprocal cutoff constant. -/
theorem oddClass_high_cutoff_scale_identity {kappa X : ℝ}
    (hX : Real.exp 1 < X) :
    (Real.sqrt X / Real.log X) *
        ((X / Real.sqrt (Real.log X)) / classAverageCutoff kappa X) =
      (1 / kappa) * oddClassAverageScale X := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  calc
    (Real.sqrt X / Real.log X) *
        ((X / Real.sqrt (Real.log X)) / classAverageCutoff kappa X) =
        (Real.sqrt X / Real.log X) * (X / Real.sqrt (Real.log X)) *
          (1 / classAverageCutoff kappa X) := by ring
    _ = (Real.sqrt X / Real.log X) * (X / Real.sqrt (Real.log X)) *
          ((1 / kappa) *
            Real.sqrt (Real.log (Real.log X) / Real.log X)) := by
      rw [one_div_classAverageCutoff]
    _ = (1 / kappa) * oddClassAverageScale X := by
      rw [oddClassAverageScale_eq_base_mul_saving_div_sqrt hX,
        rpow_three_halves_eq_mul_sqrt hXpos]
      ring

/-- The low-regulator scale produced after an exceptional-set saving of
`(log X)^(-2)` is stronger than the headline scale in the standard large
logarithmic range. -/
theorem oddClass_low_scale_le {X : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) :
    (Real.sqrt X / Real.log X) * (X / (Real.log X) ^ 2) ≤
      oddClassAverageScale X := by
  have hlogs := classAverage_large_log_bounds hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans hlogs.1
  have hlog : 0 < Real.log X := classAverageCutoff_log_pos hlogs.1
  have hloglog : 1 ≤ Real.log (Real.log X) := hlogs.2
  have hsqrt : 1 ≤ Real.sqrt (Real.log (Real.log X)) :=
    Real.one_le_sqrt.mpr hloglog
  have hone : 1 / Real.log X ≤ Real.sqrt (Real.log (Real.log X)) := by
    have hlogone : 1 ≤ Real.log X :=
      (one_lt_log_of_exp_one_lt hlogs.1).le
    exact ((div_le_one₀ hlog).2 hlogone).trans hsqrt
  have hbase : 0 ≤ Real.rpow X (3 / 2) / (Real.log X) ^ 2 := by
    exact div_nonneg (Real.rpow_nonneg hXpos.le _) (sq_nonneg _)
  rw [oddClassAverageScale]
  calc
    (Real.sqrt X / Real.log X) * (X / (Real.log X) ^ 2) =
        (Real.rpow X (3 / 2) / (Real.log X) ^ 2) *
          (1 / Real.log X) := by
      rw [rpow_three_halves_eq_mul_sqrt hXpos]
      field_simp [hlog.ne']
    _ ≤ (Real.rpow X (3 / 2) / (Real.log X) ^ 2) *
        Real.sqrt (Real.log (Real.log X)) :=
      mul_le_mul_of_nonneg_left hone hbase
    _ = Real.rpow X (3 / 2) * Real.sqrt (Real.log (Real.log X)) /
        (Real.log X) ^ 2 := by ring

end

end PellPaper
