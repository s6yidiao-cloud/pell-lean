import Pell.SlopeLatticeBallGrowth
import Pell.Main3LargeAnalyticFixedKeyCellTargetLatticeGeometry
import Mathlib.Tactic

/-!
# Ball growth for an integral lattice in one complex embedding

The real and imaginary parts of `x + omega*y` can be written as one of the
project's normalized slope maps.  Scaling both coordinates by two makes a
unit lower bound for the complex norm into a unit lower bound for the actual
first slope minimum.  The existing normalized lattice theorem then gives the
linear-plus-area count with the literal determinant factor `|omega.im|`.
-/

namespace PellPaper

noncomputable section

/-- The displayed slope map is exactly twice the coordinate sup norm of the
complex integral linear form. -/
theorem slopeVectorSupNorm_complexIntegralLinearForm_eq
    (omega : ℂ) (homegaIm : omega.im ≠ 0) (y : Fin 2 → ℤ) :
    slopeVectorSupNorm (1 / (2 * |omega.im|)) 1 2
        (-omega.re / |omega.im|) (y 0, y 1) =
      2 * max
        |(main3IntegralTargetLinearForm omega y).re|
        |(main3IntegralTargetLinearForm omega y).im| := by
  have hb : 0 < |omega.im| := abs_pos.mpr homegaIm
  have hfirst :
      2 * (y 0 : ℝ) / 1 -
          (-omega.re / |omega.im|) * (y 1 : ℝ) /
            (1 / (2 * |omega.im|)) =
        2 * (main3IntegralTargetLinearForm omega y).re := by
    simp only [main3IntegralTargetLinearForm, Complex.add_re,
      Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
      mul_zero, sub_zero, div_one]
    field_simp [hb.ne']
    ring
  have hsecond :
      |(y 1 : ℝ) / (1 / (2 * |omega.im|))| =
        2 * |(main3IntegralTargetLinearForm omega y).im| := by
    simp only [main3IntegralTargetLinearForm, Complex.add_im,
      Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
      zero_add]
    have hden : (y 1 : ℝ) / (1 / (2 * |omega.im|)) =
        2 * |omega.im| * (y 1 : ℝ) := by
      field_simp [hb.ne']
    rw [hden, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_abs]
    simp only [mul_zero, zero_add, abs_mul]
    ring
  rw [slopeVectorSupNorm, hfirst, hsecond, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_max_of_nonneg]
  norm_num

/-- The complex norm is bounded by the corresponding doubled coordinate sup
norm. -/
theorem norm_main3IntegralTargetLinearForm_le_slopeVectorSupNorm
    (omega : ℂ) (homegaIm : omega.im ≠ 0) (y : Fin 2 → ℤ) :
    ‖main3IntegralTargetLinearForm omega y‖ ≤
      slopeVectorSupNorm (1 / (2 * |omega.im|)) 1 2
        (-omega.re / |omega.im|) (y 0, y 1) := by
  rw [slopeVectorSupNorm_complexIntegralLinearForm_eq omega homegaIm y]
  let A := max |(main3IntegralTargetLinearForm omega y).re|
    |(main3IntegralTargetLinearForm omega y).im|
  have hA : 0 ≤ A :=
    (abs_nonneg _).trans (le_max_left _ _)
  have hre : |(main3IntegralTargetLinearForm omega y).re| ≤ A :=
    le_max_left _ _
  have him : |(main3IntegralTargetLinearForm omega y).im| ≤ A :=
    le_max_right _ _
  have hreSq : (main3IntegralTargetLinearForm omega y).re ^ 2 ≤ A ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _ ) hA).2 hre
    simpa only [sq_abs] using this
  have himSq : (main3IntegralTargetLinearForm omega y).im ^ 2 ≤ A ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _ ) hA).2 him
    simpa only [sq_abs] using this
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hA)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

/-- Conversely, the doubled coordinate sup norm is at most twice the complex
norm. -/
theorem slopeVectorSupNorm_complexIntegralLinearForm_le_two_mul_norm
    (omega : ℂ) (homegaIm : omega.im ≠ 0) (y : Fin 2 → ℤ) :
    slopeVectorSupNorm (1 / (2 * |omega.im|)) 1 2
        (-omega.re / |omega.im|) (y 0, y 1) ≤
      2 * ‖main3IntegralTargetLinearForm omega y‖ := by
  rw [slopeVectorSupNorm_complexIntegralLinearForm_eq omega homegaIm y]
  gcongr
  exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

/-- A finite nonzero family in a complex-norm ball has linear-plus-area
growth.  The assumption `hnormOne` is global because it supplies the lower
bound for the actual first minimum, whose attaining vector need not lie in
`T`. -/
theorem card_complexIntegralLinearForm_norm_le_linear_add_area
    (T : Finset (Fin 2 → ℤ)) (omega : ℂ) (H : ℝ)
    (homegaIm : omega.im ≠ 0) (hH : 1 ≤ H)
    (hnormOne : ∀ y : Fin 2 → ℤ, y ≠ 0 →
      1 ≤ ‖main3IntegralTargetLinearForm omega y‖)
    (hnonzero : ∀ y ∈ T, y ≠ 0)
    (hball : ∀ y ∈ T, ‖main3IntegralTargetLinearForm omega y‖ ≤ H) :
    (T.card : ℝ) ≤ 12 * H + 36 * H ^ 2 / |omega.im| := by
  let b := |omega.im|
  let U := 1 / (2 * b)
  let V : ℝ := 1
  let M : ℝ := 2
  let z := -omega.re / b
  have hb : 0 < b := by
    dsimp only [b]
    exact abs_pos.mpr homegaIm
  have hU : 0 < U := by dsimp only [U]; positivity
  have hV : 0 < V := by dsimp only [V]; norm_num
  have hM : 0 < M := by dsimp only [M]; norm_num
  have hRadius : (1 : ℝ) ≤ 2 * H := by nlinarith
  have hmuOne : 1 ≤ firstSlopeSupNorm U V M z := by
    obtain ⟨p, hp, hpmin⟩ :=
      exists_nonzero_slopeVector_attaining_firstSupNorm U V M z hU hV hM
    let y : Fin 2 → ℤ := ![p.1, p.2]
    have hy : y ≠ 0 := by
      intro hyzero
      apply hp
      have hy0 : y 0 = 0 := by rw [hyzero]; rfl
      have hy1 : y 1 = 0 := by rw [hyzero]; rfl
      have hp0 : p.1 = 0 := by simpa [y] using hy0
      have hp1 : p.2 = 0 := by simpa [y] using hy1
      change p = (0, 0)
      exact Prod.ext hp0 hp1
    have hone := hnormOne y hy
    have hnormSlope :=
      norm_main3IntegralTargetLinearForm_le_slopeVectorSupNorm
        omega homegaIm y
    have hpairs : (y 0, y 1) = p := by
      simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one]
    change 1 ≤ firstSlopeSupNorm U V M z
    rw [← hpmin]
    simpa only [U, V, M, z, b, hpairs] using hone.trans hnormSlope
  have hslopeBall : ∀ y ∈ T,
      slopeVectorSupNorm U V M z (y 0, y 1) ≤ 2 * H := by
    intro y hy
    have hslope :=
      slopeVectorSupNorm_complexIntegralLinearForm_le_two_mul_norm
        omega homegaIm y
    have hnorm := hball y hy
    simpa only [U, V, M, z, b] using
      hslope.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  have hcount := card_slopeVectorSupNorm_le_linear_add_area
    T U V M z (2 * H) hU hV hM hRadius hmuOne hnonzero hslopeBall
  calc
    (T.card : ℝ) ≤ 6 * (2 * H) +
        36 * (2 * H) ^ 2 / (M / (U * V)) := hcount
    _ = 12 * H + 36 * H ^ 2 / |omega.im| := by
      dsimp only [M, U, V, b]
      field_simp [hb.ne']
      ring

end

end PellPaper
