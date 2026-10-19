import Mathlib.Tactic

/-!
# Absorbing a reciprocal height window into a linear theta budget

The literal quadratic-form orbit count uses the reciprocal lower endpoint
`A / H`.  If `A` is at least one, then its logarithmic window costs at most
twice `log H`.  Combining a coarse height budget with a `1/12` regulator
lower bound gives the deliberately rounded capacity `1024 * theta`.
-/

namespace PellPaper

noncomputable section

/-- An abstract reciprocal-window signed-power capacity is at most
`1024 * theta` under the logarithmic height and regulator budgets used in
the main3 large-analytic target fibre. -/
theorem two_mul_one_add_reciprocal_height_log_capacity_le_1024_mul_theta
    {theta H A eta : ℝ} {Y : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hH : 0 < H) (hA : 1 ≤ A)
    (hlogH : Real.log H ≤ 21 * theta * Real.log (Y : ℝ))
    (hlogEta : Real.log (Y : ℝ) / 12 < Real.log eta) :
    2 * (1 + Real.log (H / (A / H)) / Real.log eta) ≤
      1024 * theta := by
  have hYone : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos hYone
  have hlogEtaPos : 0 < Real.log eta :=
    (div_pos hlogYpos (by norm_num)).trans hlogEta
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hlogAnonneg : 0 ≤ Real.log A := Real.log_nonneg hA
  have hwindowLog :
      Real.log (H / (A / H)) = 2 * Real.log H - Real.log A := by
    rw [Real.log_div hH.ne' (div_ne_zero hApos.ne' hH.ne'),
      Real.log_div hApos.ne' hH.ne']
    ring
  have hwindowLogUpper :
      Real.log (H / (A / H)) ≤
        42 * theta * Real.log (Y : ℝ) := by
    rw [hwindowLog]
    linarith
  have hscaledRegulator :
      42 * theta * Real.log (Y : ℝ) <
        (504 * theta) * Real.log eta := by
    have hthetaPos : 0 < 504 * theta := by positivity
    have hmul := mul_lt_mul_of_pos_left hlogEta hthetaPos
    calc
      42 * theta * Real.log (Y : ℝ) =
          (504 * theta) * (Real.log (Y : ℝ) / 12) := by ring
      _ < (504 * theta) * Real.log eta := hmul
  have hquotient :
      Real.log (H / (A / H)) / Real.log eta ≤ 504 * theta := by
    apply (div_le_iff₀ hlogEtaPos).2
    exact hwindowLogUpper.trans hscaledRegulator.le
  linarith

end

end PellPaper
