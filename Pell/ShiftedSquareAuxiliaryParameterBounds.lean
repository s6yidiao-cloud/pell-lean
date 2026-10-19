import Pell.ShiftedSquareContentScaleBounds
import Pell.ShiftedSquareExplicitIntegralBasisHeight
import Mathlib.Tactic

/-!
# Finite ranges for shifted-square auxiliary parameters

The large-block determinant argument sums over the contents and the fixed
quadratic-order coefficients before counting primitive coordinate pairs.
This module turns the existing real Minkowski bound and divisibility facts
into explicit natural-number ranges.  It is only a finite-parameter adapter;
it contains no coordinate or block count.
-/

namespace PellPaper

noncomputable section

/-- For a nonzero integral shift, its square root is bounded by its natural
absolute value. -/
theorem shiftedSquare_sqrt_abs_le_natAbs
    {a : ℤ} (ha : a ≠ 0) :
    Real.sqrt |(a : ℝ)| ≤ (a.natAbs : ℝ) := by
  have haNat : 1 ≤ a.natAbs := (Nat.one_le_iff_ne_zero).2
    (Int.natAbs_ne_zero.mpr ha)
  have habs : |(a : ℝ)| = (a.natAbs : ℝ) := by
    calc
      |(a : ℝ)| = ((|a| : ℤ) : ℝ) :=
        (Int.cast_abs (R := ℝ) (a := a)).symm
      _ = (a.natAbs : ℝ) := (Nat.cast_natAbs (α := ℝ) a).symm
  rw [habs]
  exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast haNat))

/-- The Minkowski index ranges over at most a linear interval in `|a|`. -/
theorem shiftedSquare_C₀_le_thirtytwo_mul_natAbs
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.minkowski.C₀ ≤ 32 * a.natAbs := by
  have hsqrt := shiftedSquare_sqrt_abs_le_natAbs ha
  have hreal : (P.minkowski.C₀ : ℝ) ≤ 32 * (a.natAbs : ℝ) :=
    P.minkowski.C₀_le_thirtytwo_mul_sqrt_abs.trans
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  exact_mod_cast hreal

/-- Removing the source content costs at most twice the Minkowski index. -/
theorem shiftedSquare_sourceContent_le_two_mul_C₀
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.r ≤ 2 * P.minkowski.C₀ := by
  have hsquare := shiftedSquare_sourceContent_sq_le_two_mul_C₀_sq P
  nlinarith [sq_nonneg (P.r : ℤ), sq_nonneg (P.minkowski.C₀ : ℤ)]

/-- The source content therefore also ranges over a linear interval in the
shift. -/
theorem shiftedSquare_sourceContent_le_sixtyfour_mul_natAbs
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.r ≤ 64 * a.natAbs := by
  calc
    P.r ≤ 2 * P.minkowski.C₀ := shiftedSquare_sourceContent_le_two_mul_C₀ P
    _ ≤ 2 * (32 * a.natAbs) :=
      Nat.mul_le_mul_left 2 (shiftedSquare_C₀_le_thirtytwo_mul_natAbs ha P)
    _ = 64 * a.natAbs := by ring

/-- The squarefree-target normalization makes the target content no larger
than the Minkowski index. -/
theorem shiftedSquare_targetContent_le_C₀
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.ell ≤ P.minkowski.C₀ :=
  Nat.le_of_dvd P.minkowski.C₀_pos P.ell_dvd_C₀

/-- The target content ranges over the same linear shift interval. -/
theorem shiftedSquare_targetContent_le_thirtytwo_mul_natAbs
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.ell ≤ 32 * a.natAbs :=
  (shiftedSquare_targetContent_le_C₀ P).trans
    (shiftedSquare_C₀_le_thirtytwo_mul_natAbs ha P)

/-- Complete explicit finite ranges for the auxiliary scalar data and the
fixed-basis structure constant. -/
theorem shiftedSquare_auxiliaryParameterBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.minkowski.C₀ ≤ 32 * a.natAbs ∧
      P.r ≤ 64 * a.natAbs ∧
      P.ell ≤ 32 * a.natAbs ∧
      P.bζ.natAbs ≤ 2 ∧
      P.c.natAbs ≤ 4 * a.natAbs + 1 := by
  refine ⟨shiftedSquare_C₀_le_thirtytwo_mul_natAbs ha P,
    shiftedSquare_sourceContent_le_sixtyfour_mul_natAbs ha P,
    shiftedSquare_targetContent_le_thirtytwo_mul_natAbs ha P, ?_, ?_⟩
  · have hb : (P.bζ.natAbs : ℤ) ≤ (2 : ℤ) := by
      simpa only [Int.natCast_natAbs] using P.abs_bζ_le_two
    exact_mod_cast hb
  · exact natAbs_shiftedSquareExplicitIntegralBasis_constant_le
      P.basis P.omega P.t P.c P.basis_zero P.basis_one
        P.t_zero_or_one P.omega_sq

end

end PellPaper
