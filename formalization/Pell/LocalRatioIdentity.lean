import Pell.NormalizedFactorIdentity
import Pell.ShiftedSquareReduction

/-!
# Local ratio coordinates near the Pell parabola

For a chosen nonzero local centre `s₀`, the manuscript uses
`S = (d/e)/s₀` and `T = (v/u)/s₀²`.  This file proves the exact identity for
`T - S²` and records its nonvanishing for the four Pell differences.  It is
the elementary algebra that permits factors of `t - s²` to be removed from
an auxiliary curve.
-/

namespace PellPaper

/-- The two normalized local coordinates used in the determinant argument. -/
noncomputable def localSourceRatio (s₀ : ℝ) (d e : ℕ) : ℝ :=
  ((d : ℝ) / (e : ℝ)) / s₀

noncomputable def localTargetRatio (s₀ : ℝ) (u v : ℕ) : ℝ :=
  ((v : ℝ) / (u : ℝ)) / s₀ ^ 2

/-- After localization at a nonzero centre, the exact factor difference is
the displayed displacement from the parabola. -/
theorem local_ratio_parabola_identity {d e u v : ℕ} {h : ℤ} {s₀ : ℝ}
    (hs₀ : s₀ ≠ 0) (he : 0 < e) (hu : 0 < u)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2 =
      (h : ℝ) / (s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ)) := by
  unfold localTargetRatio localSourceRatio
  obtain ⟨he0, hu0, _⟩ := normalized_factor_denominators_ne_zero he hu
  have hs₀sq : s₀ ^ 2 ≠ 0 := pow_ne_zero _ hs₀
  have hbase := normalized_factor_identity he hu hdiff
  field_simp [he0, hu0, hs₀sq] at hbase ⊢
  nlinarith [hbase]

/-- The local displacement is nonzero for the four possible factor
differences.  This is the precise algebraic fact needed before discarding a
factor of `t - s²` from an auxiliary polynomial. -/
theorem local_ratio_parabola_deviation_ne_zero {d e u v : ℕ} {h : ℤ} {s₀ : ℝ}
    (hs₀ : s₀ ≠ 0) (he : 0 < e) (hu : 0 < u)
    (hh : IsSignedDyadicDifference h)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2 ≠ 0 := by
  rw [local_ratio_parabola_identity hs₀ he hu hdiff]
  apply div_ne_zero
  · exact_mod_cast isSignedDyadicDifference_ne_zero hh
  · have heR : (0 : ℝ) < e := by exact_mod_cast he
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    exact ne_of_gt (mul_pos (mul_pos (sq_pos_of_ne_zero hs₀)
      (sq_pos_of_pos heR)) huR)

/-- Every tuple in the finite factor set has a nonzero local parabola
displacement at every nonzero centre. -/
theorem dyadicFactorCondition_local_ratio_parabola_deviation_ne_zero
    {θ : ℝ} {Y d e u v : ℕ} {s₀ : ℝ} (hs₀ : s₀ ≠ 0)
    (hcond : DyadicFactorCondition θ Y d e u v) :
    localTargetRatio s₀ u v - (localSourceRatio s₀ d e) ^ 2 ≠ 0 := by
  obtain ⟨h, hh, hdiff⟩ := dyadicFactorCondition_exists_difference hcond
  rcases hcond with ⟨_, he, hu, _, _⟩
  exact local_ratio_parabola_deviation_ne_zero hs₀ he hu
    (by rcases hh with rfl | rfl | rfl | rfl <;> simp [IsSignedDyadicDifference]) hdiff

end PellPaper
