import Pell.QuadraticSourceTargetCenterWindows
import Pell.DyadicTargetSlopeIntegerCover

/-!
# A genuine source-cell to target-index window

The quadratic source center is normalized by `z=M*E*s₀/D` and the scale
ratio is literally `R=D²*U/(E²*V)`.  A source multiplicative cell of width
`1+1/M`, the actual factor error at most two, and `M≤E²V` imply that the
target right-ceiling index lies within `12R+3` of `R*z²/M`.
The endpoint hypotheses `E≤e` and `U≤u` are weak, matching the existing
project's `Ico` dyadic boxes.  No source index is identified with an integer
grid, and no curve-count or weighted-sum transfer is claimed.
-/

namespace PellPaper

noncomputable section

/-- The actual scale ratio governing the quadratic source-center transport. -/
def sourceTargetScaleRatio (D E U V : ℝ) : ℝ := D ^ 2 * U / (E ^ 2 * V)

/-- The literal normalized source center. -/
def normalizedSourceSlopeCenter (D E M s₀ : ℝ) : ℝ := M * E * s₀ / D

/-- Normalization intertwines the quadratic center map with the square of
the source ratio, with all denominators explicit. -/
theorem quadraticTargetCenter_normalizedSourceSlopeCenter
    (D E U V M s : ℝ) (hD : D ≠ 0) (hE : E ≠ 0) (hM : M ≠ 0) :
    quadraticTargetCenter M (sourceTargetScaleRatio D E U V)
      (normalizedSourceSlopeCenter D E M s) = (M * U / V) * s ^ 2 := by
  dsimp [quadraticTargetCenter, sourceTargetScaleRatio, normalizedSourceSlopeCenter]
  field_simp

private theorem quadraticTargetCenter_cell_variation_le
    (M R z x : ℝ) (hM : 1 ≤ M) (hR : 0 ≤ R) (hz : 0 ≤ z ∧ z ≤ 2 * M)
    (hx : z ≤ x ∧ x ≤ z * (1 + 1 / M)) :
    |quadraticTargetCenter M R x - quadraticTargetCenter M R z| ≤ 12 * R := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hdiv : z / M ≤ 2 := (div_le_iff₀ hMpos).mpr hz.2
  have hstep : z * (1 + 1 / M) = z + z / M := by ring
  have hdiff : 0 ≤ x - z ∧ x - z ≤ 2 := by rw [hstep] at hx; constructor <;> linarith
  have hxnonneg : 0 ≤ x := hz.1.trans hx.1
  have hsum : 0 ≤ x + z ∧ x + z ≤ 6 * M := by
    rw [hstep] at hx
    constructor <;> linarith
  have hprod : (x - z) * (x + z) ≤ 2 * (6 * M) :=
    mul_le_mul hdiff.2 hsum.2 hsum.1 (by norm_num)
  have heq : quadraticTargetCenter M R x - quadraticTargetCenter M R z =
      (R / M) * ((x - z) * (x + z)) := by dsimp [quadraticTargetCenter]; ring
  rw [heq, abs_of_nonneg (mul_nonneg (div_nonneg hR hMpos.le) (mul_nonneg hdiff.1 hsum.1))]
  calc
    (R / M) * ((x - z) * (x + z)) ≤ (R / M) * (2 * (6 * M)) :=
      mul_le_mul_of_nonneg_left hprod (div_nonneg hR hMpos.le)
    _ = 12 * R := by field_simp; ring

/-- The actual factor error at most two stays at most two after target
normalization, under the literal scale condition `M≤E²V`. -/
theorem abs_scaled_target_ratio_sub_source_square_le_two
    (E U V M d e u v : ℝ) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V) (hM : 0 ≤ M)
    (he : E ≤ e) (hu : U ≤ u) (hscale : M ≤ E ^ 2 * V)
    (hdiff : |e ^ 2 * v - d ^ 2 * u| ≤ 2) :
    |M * U * v / (V * u) - (M * U / V) * (d / e) ^ 2| ≤ 2 := by
  have hepos : 0 < e := hE.trans_le he
  have hupos : 0 < u := hU.trans_le hu
  have hdenpos : 0 < E ^ 2 * U := by positivity
  have hdenle : E ^ 2 * U ≤ e ^ 2 * u :=
    mul_le_mul (pow_le_pow_left₀ hE.le he 2) hu hU.le (sq_nonneg e)
  have heq : M * U * v / (V * u) - (M * U / V) * (d / e) ^ 2 =
      ((M * U / V) * (e ^ 2 * v - d ^ 2 * u)) / (e ^ 2 * u) := by field_simp
  rw [heq, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ M * U / V),
    abs_of_pos (by positivity : 0 < e ^ 2 * u)]
  calc
    (M * U / V) * |e ^ 2 * v - d ^ 2 * u| / (e ^ 2 * u) ≤
        (M * U / V) * 2 / (e ^ 2 * u) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiff (by positivity)) (by positivity)
    _ ≤ (M * U / V) * 2 / (E ^ 2 * U) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hdenle
    _ = 2 * M / (E ^ 2 * V) := by field_simp
    _ ≤ 2 := (div_le_iff₀ (by positivity : 0 < E ^ 2 * V)).mpr (by nlinarith)

/-- An actual source cell and the actual Pell-type factor error force the
target ceiling index into the explicit quadratic-center window. -/
theorem targetSlopeRightIndex_within_source_window
    (D E U V M s₀ : ℝ) (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hM : 1 ≤ M) (hs₀ : 0 ≤ s₀)
    (hzupper : normalizedSourceSlopeCenter D E M s₀ ≤ 2 * M)
    (d e u v : ℤ) (he : E ≤ (e : ℝ)) (hu : U ≤ (u : ℝ))
    (hcell : s₀ ≤ (d : ℝ) / (e : ℝ) ∧ (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M))
    (hscale : M ≤ E ^ 2 * V)
    (hdiff : |(e : ℝ) ^ 2 * (v : ℝ) - (d : ℝ) ^ 2 * (u : ℝ)| ≤ 2) :
    |(targetSlopeRightIndex U V M u v : ℝ) -
      quadraticTargetCenter M (sourceTargetScaleRatio D E U V)
        (normalizedSourceSlopeCenter D E M s₀)| ≤ 12 * sourceTargetScaleRatio D E U V + 3 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let z := normalizedSourceSlopeCenter D E M s₀
  let x := normalizedSourceSlopeCenter D E M ((d : ℝ) / (e : ℝ))
  let R := sourceTargetScaleRatio D E U V
  let t := M * U * (v : ℝ) / (V * (u : ℝ))
  let k := targetSlopeRightIndex U V M u v
  have hR : 0 ≤ R := by dsimp [R, sourceTargetScaleRatio]; positivity
  have hz : 0 ≤ z ∧ z ≤ 2 * M := ⟨by dsimp [z, normalizedSourceSlopeCenter]; positivity, hzupper⟩
  have hfactor : 0 ≤ M * E / D := by positivity
  have hx : z ≤ x ∧ x ≤ z * (1 + 1 / M) := by
    dsimp [z, x, normalizedSourceSlopeCenter]
    constructor
    · simpa only [mul_div_right_comm] using mul_le_mul_of_nonneg_left hcell.1 hfactor
    · have hbound := mul_le_mul_of_nonneg_left hcell.2 hfactor
      calc
        M * E * ((d : ℝ) / (e : ℝ)) / D = (M * E / D) * ((d : ℝ) / (e : ℝ)) := by ring
        _ ≤ (M * E / D) * (s₀ * (1 + 1 / M)) := hbound
        _ = (M * E * s₀ / D) * (1 + 1 / M) := by ring
  have hvariation := quadraticTargetCenter_cell_variation_le M R z x hM hR hz hx
  have herror : |t - quadraticTargetCenter M R x| ≤ 2 := by
    dsimp [t, x, R]
    rw [quadraticTargetCenter_normalizedSourceSlopeCenter D E U V M _ hD.ne' hE.ne' hMpos.ne']
    exact abs_scaled_target_ratio_sub_source_square_le_two E U V M
      (d : ℝ) (e : ℝ) (u : ℝ) (v : ℝ) hE hU hV hMpos.le he hu hscale hdiff
  have hceil : |(k : ℝ) - t| ≤ 1 := by
    have hd := targetSlopeRightIndex_displacement U V M u v
    rw [abs_sub_comm]
    exact abs_le.mpr ⟨hd.1.le, hd.2.trans (by norm_num)⟩
  calc
    |(k : ℝ) - quadraticTargetCenter M R z| ≤
        |(k : ℝ) - t| + |t - quadraticTargetCenter M R x| +
          |quadraticTargetCenter M R x - quadraticTargetCenter M R z| := by
      have h₁ := abs_sub_le (k : ℝ) t (quadraticTargetCenter M R z)
      have h₂ := abs_sub_le t (quadraticTargetCenter M R x) (quadraticTargetCenter M R z)
      linarith
    _ ≤ 12 * R + 3 := by linarith

end

end PellPaper
