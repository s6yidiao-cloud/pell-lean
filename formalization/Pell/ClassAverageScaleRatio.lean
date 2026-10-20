import Pell.ClassFiniteInitialRange

/-!
# A uniform ratio bound for the class-average scale

This elementary comparison isolates the regular variation needed when a
fundamental-discriminant estimate is summed over square conductors.
-/

namespace PellPaper

noncomputable section

private theorem classAverageScale_ratio_power_identity {Y X : ℝ}
    (hY : 0 < Y) (hX : 0 < X) :
    Y ^ (3 / 2 : ℝ) * (X / Y) ^ (1 / 4 : ℝ) =
      (Y / X) ^ (5 / 4 : ℝ) * X ^ (3 / 2 : ℝ) := by
  have hYX : Y * (X / Y) = X := by field_simp
  have hXY : (Y / X) * X = Y := by field_simp
  calc
    Y ^ (3 / 2 : ℝ) * (X / Y) ^ (1 / 4 : ℝ) =
        (Y ^ (5 / 4 : ℝ) * Y ^ (1 / 4 : ℝ)) *
          (X / Y) ^ (1 / 4 : ℝ) := by
            rw [show (3 / 2 : ℝ) = 5 / 4 + 1 / 4 by norm_num,
              Real.rpow_add hY]
    _ = Y ^ (5 / 4 : ℝ) *
        (Y ^ (1 / 4 : ℝ) * (X / Y) ^ (1 / 4 : ℝ)) := by ring
    _ = Y ^ (5 / 4 : ℝ) * (Y * (X / Y)) ^ (1 / 4 : ℝ) := by
      congr 1
      exact (Real.mul_rpow hY.le (div_nonneg hX.le hY.le)).symm
    _ = Y ^ (5 / 4 : ℝ) * X ^ (1 / 4 : ℝ) := by rw [hYX]
    _ = ((Y / X) * X) ^ (5 / 4 : ℝ) * X ^ (1 / 4 : ℝ) := by rw [hXY]
    _ = ((Y / X) ^ (5 / 4 : ℝ) * X ^ (5 / 4 : ℝ)) *
        X ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (div_nonneg hY.le hX.le) hX.le]
    _ = (Y / X) ^ (5 / 4 : ℝ) *
        (X ^ (5 / 4 : ℝ) * X ^ (1 / 4 : ℝ)) := by ring
    _ = (Y / X) ^ (5 / 4 : ℝ) * X ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 5 / 4 + 1 / 4 by norm_num,
        Real.rpow_add hX]

/-- There is one positive constant comparing the class-average scale at all
nested cutoffs `3 ≤ Y ≤ X`, with the power saving `(Y/X)^(5/4)`. -/
theorem exists_pos_classAverageScale_le_ratio_rpow :
    ∃ K : ℝ, 0 < K ∧ ∀ Y X : ℝ, 3 ≤ Y → Y ≤ X →
      classAverageScale Y ≤
        K * (Y / X) ^ (5 / 4 : ℝ) * classAverageScale X := by
  refine ⟨(7 : ℝ) ^ (3 / 2 : ℝ), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro Y X hYthree hYX
  have hYpos : 0 < Y := by linarith
  have hXpos : 0 < X := hYpos.trans_le hYX
  have hYone : 1 < Y := by linarith
  have hXone : 1 < X := hYone.trans_le hYX
  have hlogY : 0 < Real.log Y := Real.log_pos hYone
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hExpY : Real.exp 1 < Y := Real.exp_one_lt_three.trans_le hYthree
  have hlogYone : 1 < Real.log Y := one_lt_log_of_exp_one_lt hExpY
  have hloglogY : 0 < Real.log (Real.log Y) := Real.log_pos hlogYone
  have hlogYX : Real.log Y ≤ Real.log X := Real.log_le_log hYpos hYX
  have hloglogYX : Real.log (Real.log Y) ≤ Real.log (Real.log X) :=
    Real.log_le_log hlogY hlogYX
  have hsqrt : Real.sqrt (Real.log (Real.log Y)) ≤
      Real.sqrt (Real.log (Real.log X)) := Real.sqrt_le_sqrt hloglogYX
  let t : ℝ := X / Y
  have htpos : 0 < t := div_pos hXpos hYpos
  have htone : 1 ≤ t := by
    apply (le_div_iff₀ hYpos).mpr
    simpa using hYX
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg htone
  have htSixthOne : 1 ≤ t ^ (1 / 6 : ℝ) :=
    Real.one_le_rpow htone (by norm_num)
  have hlogt := Real.log_le_rpow_div htpos.le (by norm_num : (0 : ℝ) < 1 / 6)
  have hlogtBound : 1 + Real.log t ≤ 7 * t ^ (1 / 6 : ℝ) := by
    have hlogt' : Real.log t ≤ 6 * t ^ (1 / 6 : ℝ) := by
      calc
        Real.log t ≤ t ^ (1 / 6 : ℝ) / (1 / 6) := hlogt
        _ = 6 * t ^ (1 / 6 : ℝ) := by ring
    nlinarith
  have hlogXeq : Real.log X = Real.log Y + Real.log t := by
    have hmul : Y * t = X := by dsimp [t]; field_simp
    rw [← hmul, Real.log_mul hYpos.ne' htpos.ne']
  have hlogXBound : Real.log X ≤ Real.log Y * (7 * t ^ (1 / 6 : ℝ)) := by
    rw [hlogXeq]
    calc
      Real.log Y + Real.log t ≤ Real.log Y * (1 + Real.log t) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlogYone.le) hlogt0]
      _ ≤ Real.log Y * (7 * t ^ (1 / 6 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogtBound hlogY.le
  have hlogPowBound :
      (Real.log X) ^ (3 / 2 : ℝ) ≤
        (Real.log Y) ^ (3 / 2 : ℝ) *
          ((7 : ℝ) ^ (3 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) := by
    calc
      (Real.log X) ^ (3 / 2 : ℝ) ≤
          (Real.log Y * (7 * t ^ (1 / 6 : ℝ))) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hlogX.le hlogXBound (by norm_num)
      _ = (Real.log Y) ^ (3 / 2 : ℝ) *
          (7 * t ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) := by
        exact Real.mul_rpow hlogY.le
          (mul_nonneg (by norm_num) (Real.rpow_nonneg htpos.le _))
      _ = (Real.log Y) ^ (3 / 2 : ℝ) *
          ((7 : ℝ) ^ (3 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) := by
        congr 1
        calc
          (7 * t ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) =
              (7 : ℝ) ^ (3 / 2 : ℝ) *
                (t ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) :=
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg htpos.le _)
          _ = (7 : ℝ) ^ (3 / 2 : ℝ) * t ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul htpos.le]
            norm_num
  have hnumBound :
      Y ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log Y)) ≤
        Y ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X)) :=
    mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hYpos.le _)
  have hdenYpos : 0 < (Real.log Y) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hlogY _
  have hdenXpos : 0 < (Real.log X) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hlogX _
  rw [classAverageScale, classAverageScale]
  change (Y ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log Y))) /
      (Real.log Y) ^ (3 / 2 : ℝ) ≤
    (7 : ℝ) ^ (3 / 2 : ℝ) * (Y / X) ^ (5 / 4 : ℝ) *
      ((X ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X))) /
        (Real.log X) ^ (3 / 2 : ℝ))
  rw [show (7 : ℝ) ^ (3 / 2 : ℝ) * (Y / X) ^ (5 / 4 : ℝ) *
      (X ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X)) /
        (Real.log X) ^ (3 / 2 : ℝ)) =
      ((7 : ℝ) ^ (3 / 2 : ℝ) * (Y / X) ^ (5 / 4 : ℝ) *
        (X ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X)))) /
          (Real.log X) ^ (3 / 2 : ℝ) by ring]
  rw [div_le_div_iff₀ hdenYpos hdenXpos]
  calc
    (Y ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log Y))) *
        (Real.log X) ^ (3 / 2 : ℝ) ≤
      (Y ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X))) *
        ((Real.log Y) ^ (3 / 2 : ℝ) *
          ((7 : ℝ) ^ (3 / 2 : ℝ) * t ^ (1 / 4 : ℝ))) :=
      mul_le_mul hnumBound hlogPowBound hdenXpos.le
        (mul_nonneg (Real.rpow_nonneg hYpos.le _) (Real.sqrt_nonneg _))
    _ = ((7 : ℝ) ^ (3 / 2 : ℝ) * (Y / X) ^ (5 / 4 : ℝ) *
        (X ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X)))) *
          (Real.log Y) ^ (3 / 2 : ℝ) := by
      have hpower := classAverageScale_ratio_power_identity hYpos hXpos
      change Y ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (Real.log X)) *
          ((Real.log Y) ^ (3 / 2 : ℝ) *
            ((7 : ℝ) ^ (3 / 2 : ℝ) * (X / Y) ^ (1 / 4 : ℝ))) = _
      calc
        _ = (Y ^ (3 / 2 : ℝ) * (X / Y) ^ (1 / 4 : ℝ)) *
            (Real.sqrt (Real.log (Real.log X)) *
              (Real.log Y) ^ (3 / 2 : ℝ) * (7 : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ = ((Y / X) ^ (5 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) *
            (Real.sqrt (Real.log (Real.log X)) *
              (Real.log Y) ^ (3 / 2 : ℝ) * (7 : ℝ) ^ (3 / 2 : ℝ)) := by rw [hpower]
        _ = _ := by ring

end
end PellPaper
