import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Integral determinant vanishing from a strict archimedean bound

The approximate-determinant arguments in `main.tex` first clear all row
denominators.  The resulting determinant is an integer, so a strict real
bound below one forces it to vanish.  This module isolates that exact final
integrality step; estimating the determinant and constructing the resulting
auxiliary relation are separate layers.
-/

namespace PellPaper

open Matrix

/-- An integer whose real absolute value is strictly below one is zero. -/
theorem int_eq_zero_of_abs_cast_lt_one {z : ℤ} (h : |(z : ℝ)| < 1) : z = 0 := by
  apply Int.abs_lt_one_iff.mp
  exact_mod_cast h

/-- After denominator clearing, a square integral evaluation determinant with
strict real absolute value below one vanishes exactly. -/
theorem integral_det_eq_zero_of_abs_cast_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (h : |(A.det : ℝ)| < 1) : A.det = 0 :=
  int_eq_zero_of_abs_cast_lt_one h

/-- The same conclusion stated for the determinant after embedding the
integral matrix into the reals.  This is the form most convenient after a
real determinant estimate. -/
theorem real_det_eq_zero_of_abs_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (h : |(A.map (Int.castRingHom ℝ)).det| < 1) :
    (A.map (Int.castRingHom ℝ)).det = 0 := by
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) := by
    simpa using (Int.cast_det (R := ℝ) A).symm
  rw [hcast] at h ⊢
  exact_mod_cast integral_det_eq_zero_of_abs_cast_lt_one A h

end PellPaper
