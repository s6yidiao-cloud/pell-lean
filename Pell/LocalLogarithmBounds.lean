import Pell.LocalRatioIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Elementary logarithmic bounds for local Pell coordinates

The local-ratio paragraph of `main.tex` uses two elementary analytic
consequences of a multiplicative localization.  This module proves those
consequences with the interval hypotheses visible.  It deliberately does
not derive the intervals from the Pell factor equation: the present local
algebra supplies the exact displacement from the parabola, but not the
dyadic scale comparisons needed to turn that displacement into a relative
error bound.
-/

namespace PellPaper

/-- A positive quantity in the multiplicative unit band
`[(1 + δ)⁻¹, 1 + δ]` has logarithm of absolute value at most `δ`. -/
theorem abs_log_le_of_inv_one_add_le_le_one_add
    {R δ : ℝ} (hδ : 0 ≤ δ)
    (hlower : (1 + δ)⁻¹ ≤ R) (hupper : R ≤ 1 + δ) :
    |Real.log R| ≤ δ := by
  have hbase_pos : 0 < 1 + δ := by linarith
  have hinv_pos : 0 < (1 + δ)⁻¹ := inv_pos.mpr hbase_pos
  have hR_pos : 0 < R := lt_of_lt_of_le hinv_pos hlower
  have hlog_base : Real.log (1 + δ) ≤ δ := by
    calc
      Real.log (1 + δ) ≤ (1 + δ) - 1 :=
        Real.log_le_sub_one_of_pos hbase_pos
      _ = δ := by ring
  have hlog_upper : Real.log R ≤ Real.log (1 + δ) :=
    Real.strictMonoOn_log.monotoneOn hR_pos hbase_pos hupper
  have hlog_lower : -δ ≤ Real.log R := by
    calc
      -δ ≤ -Real.log (1 + δ) := neg_le_neg hlog_base
      _ = Real.log ((1 + δ)⁻¹) := (Real.log_inv _).symm
      _ ≤ Real.log R :=
        Real.strictMonoOn_log.monotoneOn hinv_pos hR_pos hlower
  exact abs_le.mpr ⟨hlog_lower, hlog_upper.trans hlog_base⟩

/-- The one-sided source interval from the local-ratio construction implies
the stated `M⁻¹` logarithmic bound.  The source has `M ≥ 1`; this provides
the positivity needed for the reciprocal. -/
theorem abs_log_le_one_div_of_one_le_le_one_add_one_div
    {S M : ℝ} (hM : 1 ≤ M) (hlower : 1 ≤ S)
    (hupper : S ≤ 1 + 1 / M) :
    |Real.log S| ≤ 1 / M := by
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hδ : 0 ≤ 1 / M := (one_div_pos.mpr hM_pos).le
  apply abs_log_le_of_inv_one_add_le_le_one_add hδ
  · have hbase : 1 ≤ 1 + 1 / M := by linarith
    exact (inv_le_one_of_one_le₀ hbase).trans hlower
  · exact hupper

/-- Source-coordinate form of the preceding estimate.  It is directly
applicable to the interval `s₀ ≤ d/e ≤ s₀ (1 + M⁻¹)` in `main.tex`; a strict
left endpoint can of course be weakened to the displayed non-strict one. -/
theorem abs_log_localSourceRatio_le_one_div_of_localized_interval
    {s₀ M : ℝ} {d e : ℕ} (hs₀ : 0 < s₀) (hM : 1 ≤ M)
    (hlower : s₀ ≤ (d : ℝ) / (e : ℝ))
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M)) :
    |Real.log (localSourceRatio s₀ d e)| ≤ 1 / M := by
  apply abs_log_le_one_div_of_one_le_le_one_add_one_div hM
  · unfold localSourceRatio
    apply (le_div_iff₀ hs₀).mpr
    simpa using hlower
  · unfold localSourceRatio
    apply (div_le_iff₀ hs₀).mpr
    simpa [mul_comm] using hupper

/-- A multiplicative band for `T / S²` yields the second local logarithmic
bound in the exact sheared form used by the determinant matrix. -/
theorem abs_sheared_log_le_of_ratio_band
    {S T δ : ℝ} (hδ : 0 ≤ δ) (hS : 0 < S) (hT : 0 < T)
    (hlower : (1 + δ)⁻¹ ≤ T / S ^ 2)
    (hupper : T / S ^ 2 ≤ 1 + δ) :
    |Real.log T - 2 * Real.log S| ≤ δ := by
  have hratio := abs_log_le_of_inv_one_add_le_le_one_add
    (R := T / S ^ 2) hδ hlower hupper
  have hlog_ratio : Real.log (T / S ^ 2) = Real.log T - 2 * Real.log S := by
    rw [Real.log_div hT.ne' (pow_ne_zero _ hS.ne'), Real.log_pow]
    norm_num
  rw [← hlog_ratio]
  exact hratio

/-- The `X⁻¹` version of `abs_sheared_log_le_of_ratio_band`. -/
theorem abs_sheared_log_le_one_div_of_ratio_band
    {S T X : ℝ} (hX : 0 < X) (hS : 0 < S) (hT : 0 < T)
    (hlower : (1 + 1 / X)⁻¹ ≤ T / S ^ 2)
    (hupper : T / S ^ 2 ≤ 1 + 1 / X) :
    |Real.log T - 2 * Real.log S| ≤ 1 / X :=
  abs_sheared_log_le_of_ratio_band (one_div_pos.mpr hX).le hS hT hlower hupper

/-- An additive local error of size `X⁻¹` gives a relative logarithmic error
of size `2 X⁻¹` once `S ≥ 1` and `X ≥ 2`.  This is the elementary analytic
step matching the source shape `T = S² + O(X⁻¹)` when the implicit constant
has been made equal to one. -/
theorem abs_sheared_log_le_two_div_of_unit_additive_error
    {S T X : ℝ} (hX : 2 ≤ X) (hS : 1 ≤ S)
    (herror : |T - S ^ 2| ≤ 1 / X) :
    |Real.log T - 2 * Real.log S| ≤ 2 / X := by
  have hX_pos : 0 < X := by linarith
  have hX_inv_nonneg : 0 ≤ 1 / X := (one_div_pos.mpr hX_pos).le
  have hX_inv_le_half : 1 / X ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hX
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hS_sq_pos : 0 < S ^ 2 := sq_pos_of_pos hS_pos
  have hS_sq_one : 1 ≤ S ^ 2 := by
    nlinarith [sq_nonneg (S - 1)]
  rcases abs_le.mp herror with ⟨herror_lower, herror_upper⟩
  have hT_pos : 0 < T := by
    nlinarith
  have hdelta : 0 ≤ 2 / X := by positivity
  have hratio_upper : T / S ^ 2 ≤ 1 + 2 / X := by
    apply (div_le_iff₀ hS_sq_pos).mpr
    have hfactor : 0 ≤ 2 * S ^ 2 - 1 := by linarith
    have hproduct : 0 ≤ (1 / X) * (2 * S ^ 2 - 1) :=
      mul_nonneg hX_inv_nonneg hfactor
    have hcompare : S ^ 2 + 1 / X ≤ (1 + 2 / X) * S ^ 2 := by
      calc
        S ^ 2 + 1 / X =
            (1 + 2 / X) * S ^ 2 - (1 / X) * (2 * S ^ 2 - 1) := by ring
        _ ≤ (1 + 2 / X) * S ^ 2 := sub_le_self _ hproduct
    linarith
  have hratio_lower : (1 + 2 / X)⁻¹ ≤ T / S ^ 2 := by
    apply (le_div_iff₀ hS_sq_pos).mpr
    have hbase_pos : 0 < 1 + 2 / X := by positivity
    have hfactor : 0 ≤ 2 * S ^ 2 - 1 - 2 * (1 / X) := by
      nlinarith
    have hproduct : 0 ≤ (1 / X) * (2 * S ^ 2 - 1 - 2 * (1 / X)) :=
      mul_nonneg hX_inv_nonneg hfactor
    calc
      (1 + 2 / X)⁻¹ * S ^ 2 = S ^ 2 / (1 + 2 / X) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ S ^ 2 - 1 / X := by
        apply (div_le_iff₀ hbase_pos).mpr
        calc
          S ^ 2 = (S ^ 2 - 1 / X) * (1 + 2 / X) -
              (1 / X) * (2 * S ^ 2 - 1 - 2 * (1 / X)) := by ring
          _ ≤ (S ^ 2 - 1 / X) * (1 + 2 / X) := sub_le_self _ hproduct
      _ ≤ T := by linarith
  exact abs_sheared_log_le_of_ratio_band hdelta hS_pos hT_pos
    hratio_lower hratio_upper

/-- Local-coordinate specialization of the ratio-band estimate.  The
interval hypotheses are intentionally explicit: `LocalRatioIdentity` gives
an exact additive displacement, while deriving this relative band requires
the source's missing dyadic scale comparisons. -/
theorem abs_sheared_log_localRatios_le_one_div_of_ratio_band
    {s₀ X : ℝ} {d e u v : ℕ} (hX : 0 < X)
    (hS : 0 < localSourceRatio s₀ d e)
    (hT : 0 < localTargetRatio s₀ u v)
    (hlower : (1 + 1 / X)⁻¹ ≤
      localTargetRatio s₀ u v / (localSourceRatio s₀ d e) ^ 2)
    (hupper : localTargetRatio s₀ u v / (localSourceRatio s₀ d e) ^ 2 ≤
      1 + 1 / X) :
    |Real.log (localTargetRatio s₀ u v) -
        2 * Real.log (localSourceRatio s₀ d e)| ≤ 1 / X :=
  abs_sheared_log_le_one_div_of_ratio_band hX hS hT hlower hupper

/-- Additive-error local-coordinate form of the preceding elementary
estimate.  Thus an explicit numerical version of the source statement
`T = S² + O(X⁻¹)`, together with `S ≥ 1`, supplies the sheared logarithm
bound required by the determinant input. -/
theorem abs_sheared_log_localRatios_le_two_div_of_unit_additive_error
    {s₀ X : ℝ} {d e u v : ℕ} (hX : 2 ≤ X)
    (hS : 1 ≤ localSourceRatio s₀ d e)
    (herror : |localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2| ≤
      1 / X) :
    |Real.log (localTargetRatio s₀ u v) -
        2 * Real.log (localSourceRatio s₀ d e)| ≤ 2 / X :=
  abs_sheared_log_le_two_div_of_unit_additive_error hX hS herror

/-- The exact Pell displacement from `LocalRatioIdentity` can be used
directly as the explicit additive-error input.  The hypothesis `hdisplacement`
is precisely the source-side scale estimate still needed to turn the
factor-equation identity into the claimed `O(X⁻¹)` local logarithm bound. -/
theorem abs_sheared_log_localRatios_le_two_div_of_displacement_bound
    {d e u v : ℕ} {h : ℤ} {s₀ X : ℝ}
    (hs₀ : s₀ ≠ 0) (he : 0 < e) (hu : 0 < u)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h)
    (hX : 2 ≤ X) (hS : 1 ≤ localSourceRatio s₀ d e)
    (hdisplacement :
      |(h : ℝ) / (s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ))| ≤ 1 / X) :
    |Real.log (localTargetRatio s₀ u v) -
        2 * Real.log (localSourceRatio s₀ d e)| ≤ 2 / X := by
  apply abs_sheared_log_localRatios_le_two_div_of_unit_additive_error hX hS
  rw [local_ratio_parabola_identity hs₀ he hu hdiff]
  exact hdisplacement

end PellPaper
