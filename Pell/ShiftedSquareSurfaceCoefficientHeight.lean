import Pell.ShiftedSquareSurfaceForm
import Pell.BinaryQuadraticLinearEliminant
import Mathlib.Tactic

/-!
# Explicit coefficients and height of the shifted-square surface

This isolated candidate converts the special surface form into the generic
six-coefficient bidegree-`(2,1)` interface.  It also gives a coefficient
height depending only on the integral-basis constant.
-/

namespace PellPaper

/-- The six coefficients of the coefficient-of-`omega` surface when
`omega^2 = t*omega + c`.  The first index is the exponent of the second
source coordinate and the second index is the target coordinate. -/
def shiftedSquareSurfaceCoefficients (t c : ℤ) : Fin 3 → Fin 2 → ℤ :=
  ![![0, 1], ![2, 2 * t], ![t, c + t ^ 2]]

/-- A nonnegative natural coefficient-height majorant. -/
def shiftedSquareSurfaceCoefficientHeight (c : ℤ) : ℕ :=
  2 * (c.natAbs + 1)

/-- The explicit tensor evaluates to the fixed-target special quadratic
form, with source first and target second. -/
theorem quadraticLinearFormEval_shiftedSquareSurfaceCoefficients
    (t c : ℤ) (x y : Fin 2 → ℤ) :
    quadraticLinearFormEval (shiftedSquareSurfaceCoefficients t c) x y =
      (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) := by
  rw [shiftedSquareSurfaceForm_eval]
  simp [quadraticLinearFormEval, shiftedSquareSurfaceCoefficients,
    shiftedSquareSurfaceP, shiftedSquareSurfaceQ, Fin.sum_univ_succ]
  ring

/-- If `t` is one of the two integral-basis trace parameters, every one of
the six coefficients is bounded by `2*(|c|+1)`. -/
theorem abs_shiftedSquareSurfaceCoefficients_le_height
    (t c : ℤ) (ht : t = 0 ∨ t = 1) (i : Fin 3) (j : Fin 2) :
    |shiftedSquareSurfaceCoefficients t c i j| ≤
      (shiftedSquareSurfaceCoefficientHeight c : ℤ) := by
  have hcNonneg : 0 ≤ |c| := abs_nonneg c
  have hcPlus : |c + 1| ≤ 2 * (|c| + 1) := by
    calc
      |c + 1| ≤ |c| + |(1 : ℤ)| := abs_add_le c 1
      _ = |c| + 1 := by norm_num
      _ ≤ 2 * (|c| + 1) := by omega
  norm_num [shiftedSquareSurfaceCoefficientHeight]
  rcases ht with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [shiftedSquareSurfaceCoefficients]
  all_goals first | exact hcPlus | omega

end PellPaper
