import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Rounding one coordinate of an integer determinant-one completion

Right multiplication by an installed determinant-one transvection keeps
the first column and subtracts an integer multiple of it from the second.
For any additive real-valued functional nonzero on the first column,
rounding the ratio of the two column values makes the second value at
most half the absolute first value. No shortest-vector hypothesis is used.
-/

namespace PellPaper
open scoped MatrixGroups

/-- Subtract `k` copies of the first column from the second column of `W`.
The determinant-one property is supplied by the library transvection. -/
def sl2ColumnShear (W : SL(2, ℤ)) (k : ℤ) : SL(2, ℤ) :=
  W * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (-k)

@[simp]
theorem sl2ColumnShear_first_column (W : SL(2, ℤ)) (k : ℤ) (i : Fin 2) :
    sl2ColumnShear W k i 0 = W i 0 := by
  change (((W : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.transvection 0 1 (-k)) :
    Matrix (Fin 2) (Fin 2) ℤ) i 0 = _
  exact Matrix.mul_transvection_apply_of_ne 0 1 i 0 (by decide) (-k) _

theorem sl2ColumnShear_second_column (W : SL(2, ℤ)) (k : ℤ) :
    (fun i => sl2ColumnShear W k i 1) =
      (fun i => W i 1) - k • (fun i => W i 0) := by
  funext i
  change (((W : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.transvection 0 1 (-k)) :
    Matrix (Fin 2) (Fin 2) ℤ) i 1 = _
  rw [Matrix.mul_transvection_apply_same]
  simp [sub_eq_add_neg, mul_comm]

/-- Any additive real-valued functional respects the exact integer shear. -/
theorem apply_sl2ColumnShear_second_column
    (W : SL(2, ℤ)) (k : ℤ) (ell : (Fin 2 → ℤ) →+ ℝ) :
    ell (fun i => sl2ColumnShear W k i 1) =
      ell (fun i => W i 1) - (k : ℝ) * ell (fun i => W i 0) := by
  rw [sl2ColumnShear_second_column, map_sub, map_zsmul]
  simp only [zsmul_eq_mul]

/-- The rounded shear has half-width at the selected nonzero coordinate.
The first value may have either sign, and ties use the library's rounding
towards positive infinity. -/
theorem abs_apply_sl2ColumnShear_round_le
    (W : SL(2, ℤ)) (ell : (Fin 2 → ℤ) →+ ℝ)
    (h0 : ell (fun i => W i 0) ≠ 0) :
    |ell (fun i => sl2ColumnShear W
      (round (ell (fun i => W i 1) / ell (fun i => W i 0))) i 1)| ≤
        |ell (fun i => W i 0)| / 2 := by
  rw [apply_sl2ColumnShear_second_column]
  let a := ell (fun i => W i 0)
  let b := ell (fun i => W i 1)
  change |b - (round (b / a) : ℝ) * a| ≤ |a| / 2
  have ha : a ≠ 0 := h0
  calc
    |b - (round (b / a) : ℝ) * a| = |b / a - (round (b / a) : ℝ)| * |a| := by
      rw [← abs_mul]
      congr 1
      field_simp
    _ ≤ (1 / 2) * |a| := mul_le_mul_of_nonneg_right (abs_sub_round (b / a)) (abs_nonneg a)
    _ = |a| / 2 := by ring

/-- An actual determinant-one matrix with the same first column and an
explicit rounded second column satisfying the half-width bound. -/
theorem exists_sl2_rounded_column
    (W : SL(2, ℤ)) (ell : (Fin 2 → ℤ) →+ ℝ)
    (h0 : ell (fun i => W i 0) ≠ 0) :
    ∃ W' : SL(2, ℤ),
      W' = sl2ColumnShear W (round (ell (fun i => W i 1) / ell (fun i => W i 0))) ∧
      (fun i => W' i 0) = (fun i => W i 0) ∧
      (fun i => W' i 1) = (fun i => W i 1) -
        round (ell (fun i => W i 1) / ell (fun i => W i 0)) • (fun i => W i 0) ∧
      |ell (fun i => W' i 1)| ≤ |ell (fun i => W i 0)| / 2 := by
  exact ⟨_, rfl, funext (sl2ColumnShear_first_column _ _), sl2ColumnShear_second_column _ _,
    abs_apply_sl2ColumnShear_round_le W ell h0⟩

end PellPaper
