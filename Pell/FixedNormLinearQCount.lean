import Pell.FixedNormRealHeightBounds
import Pell.FixedNormPointHeightCount
import Pell.Elementary
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# An absolute linear-Q count for fixed raw Pell parameters

The counted objects are the actual positive integer pairs `(d,e)` on one
fixed signed norm level. From the literal weighted-square cutoff and the
parameters `2 ≤ Y ≤ u*v`, `2 ≤ Q`, `1 ≤ x ≤ Y^(2Q)`, this file derives
the height window, constructs a fundamental Pell solution, and proves
the absolute cardinality bound `24*Q`. No orbit or height budget is a
caller premise. Recovering fixed raw parameters from a transformed target
slope, dyadic-box specialization, and global aggregation remain separate.
-/

namespace PellPaper

/-- A finite family of actual positive integer pairs at fixed raw parameters
and one signed Pell norm level has cardinality at most `24*Q` under the
literal weighted-square and real-power cutoffs. -/
theorem card_fixedNorm_points_le_twentyFour_mul_Q
    (u v h : ℤ) (Y Q x : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hns : ¬ IsSquare (u * v))
    (hh : IsSignedDyadicDifference h)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q) (hx : 1 ≤ x)
    (hYuv : Y ≤ ((u * v : ℤ) : ℝ))
    (hxQ : x ≤ Y ^ (2 * Q))
    (S : Finset (ℤ × ℤ))
    (hpos : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2)
    (hn : ∀ z ∈ S, v * z.2 ^ 2 - u * z.1 ^ 2 = h)
    (hcut : ∀ z ∈ S, (v : ℝ) * (z.2 : ℝ) ^ 2 ≤ 8 * x) :
    (S.card : ℝ) ≤ 24 * Q := by
  let m : ℝ := ((u * v : ℤ) : ℝ)
  have hm2 : 2 ≤ m := hY.trans hYuv
  have hmpos : 0 < m := by linarith
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < Y := by linarith
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hvlem : (v : ℝ) ≤ m := by
    dsimp [m]
    rw [Int.cast_mul]
    simpa using mul_le_mul_of_nonneg_right hu1 hvpos.le
  have hmxpos : 0 < m * x := mul_pos hmpos hxpos
  let H : ℝ := 8 * Real.sqrt (m * x)
  have hmx1 : 1 ≤ m * x := by
    have hm1 : 1 ≤ m := by linarith
    simpa using mul_le_mul hm1 hx zero_le_one hmpos.le
  have hroot1 : 1 ≤ Real.sqrt (m * x) :=
    Real.le_sqrt_of_sq_le (by simpa using hmx1)
  have hH1 : 1 ≤ H := by dsimp [H]; linarith
  have hheight : ∀ z ∈ S,
      1 ≤ (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ∧
        (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ≤ H := by
    intro z hz
    obtain ⟨hlow, hupp⟩ := fixedNorm_real_value_bounds_of_signed_difference
      u v z.1 z.2 h (8 * x) hu hv (hpos z hz).1 (hpos z hz).2 hh (hn z hz) (hcut z hz)
    refine ⟨hlow, hupp.trans ?_⟩
    have hinside : (v : ℝ) * (8 * x + 2) ≤ 16 * (m * x) := by
      calc
        (v : ℝ) * (8 * x + 2) ≤ (v : ℝ) * (10 * x) :=
          mul_le_mul_of_nonneg_left (by linarith) hvpos.le
        _ ≤ m * (10 * x) :=
          mul_le_mul_of_nonneg_right hvlem (by positivity)
        _ ≤ 16 * (m * x) := by nlinarith
    have hsq : (4 * Real.sqrt (m * x)) ^ 2 = 16 * (m * x) := by
      rw [mul_pow, Real.sq_sqrt hmxpos.le]
      ring
    have hroot : Real.sqrt ((v : ℝ) * (8 * x + 2)) ≤ 4 * Real.sqrt (m * x) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity, by rw [hsq]; exact hinside⟩
    dsimp [H]
    linarith
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare (mul_pos hu hv) hns
  have hcount := card_fixedNorm_points_le_four_mul_log_height
    u v h hh ha S 1 H zero_lt_one hH1 hn hheight
  rw [div_one] at hcount
  have hlogε : 0 < Real.log (epsilon a) := Real.log_pos (one_lt_epsilon_of_isFundamental ha)
  have hlogmε : Real.log m ≤ 2 * Real.log (epsilon a) := by
    have hlt := Real.log_lt_log (Real.sqrt_pos.mpr hmpos) (sqrt_lt_epsilon ha)
    rw [Real.log_sqrt hmpos.le] at hlt
    linarith
  have hlog2m : Real.log (2 : ℝ) ≤ Real.log m := Real.log_le_log (by norm_num) hm2
  have hlogYm : Real.log Y ≤ Real.log m := Real.log_le_log hYpos hYuv
  have hlogx : Real.log x ≤ (2 * Q) * Real.log m := by
    have hlogxY := Real.log_le_log hxpos hxQ
    rw [Real.log_rpow hYpos] at hlogxY
    exact hlogxY.trans (mul_le_mul_of_nonneg_left hlogYm (by linarith))
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have hlogH : Real.log H ≤ (Q + (7 : ℝ) / 2) * Real.log m := by
    have hlogH_eq : Real.log H = Real.log 8 + (Real.log m + Real.log x) / 2 := by
      dsimp [H]
      rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hmxpos).ne',
        Real.log_sqrt hmxpos.le, Real.log_mul hmpos.ne' hxpos.ne']
    rw [hlogH_eq, hlog8]
    nlinarith
  have hlogHε : Real.log H ≤ (2 * Q + 7) * Real.log (epsilon a) := by
    have hmul := mul_le_mul_of_nonneg_left hlogmε
      (by linarith : (0 : ℝ) ≤ Q + 7 / 2)
    nlinarith
  have hquot : Real.log H / Real.log (epsilon a) ≤ 2 * Q + 7 :=
    (div_le_iff₀ hlogε).mpr hlogHε
  nlinarith

end PellPaper
