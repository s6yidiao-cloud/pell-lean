import Pell.ShiftedSquareSimultaneousNormalizedCoordinates

/-!
# Content and norm-scale bounds for normalized shifted-square coordinates

This isolated candidate extracts the scalar inequalities used before the
two-layer determinant argument in the manuscript.  The special-surface identity
controls the product of the two coordinate contents, while the divisibility
`ell ∣ C₀` gives the lower bound for the target norm scale.
-/

namespace PellPaper

noncomputable section

/-- The product of the primitive-coordinate contents divides the selected
coefficient of the scaled shifted-square element. -/
theorem shiftedSquare_contentProduct_dvd
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.r ^ 2 * P.ell ∣ P.minkowski.C₀ ^ 2 * P.bζ.natAbs := by
  have hdivInt :
      (((P.r ^ 2 * P.ell : ℕ) : ℤ)) ∣
        (P.minkowski.C₀ : ℤ) ^ 2 * P.bζ := by
    refine ⟨(shiftedSquareSurfaceForm P.t P.c P.y).eval (P.x 0) (P.x 1), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      P.special_surface_relation.symm
  have hdivAbs := Int.natAbs_dvd_natAbs.mpr hdivInt
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using hdivAbs

/-- The two primitive-coordinate contents have product at most twice the
square of the Minkowski index. -/
theorem shiftedSquare_contentProduct_le_two_mul_C₀_sq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.r ^ 2 * P.ell ≤ 2 * P.minkowski.C₀ ^ 2 := by
  have hbζ : P.bζ.natAbs ≤ 2 := by
    have hbζInt : (P.bζ.natAbs : ℤ) ≤ (2 : ℤ) := by
      simpa only [Int.natCast_natAbs] using P.abs_bζ_le_two
    exact_mod_cast hbζInt
  have hrightPos : 0 < P.minkowski.C₀ ^ 2 * P.bζ.natAbs :=
    mul_pos (pow_pos P.minkowski.C₀_pos 2)
      (Int.natAbs_pos.mpr P.bζ_ne_zero)
  calc
    P.r ^ 2 * P.ell ≤ P.minkowski.C₀ ^ 2 * P.bζ.natAbs :=
      Nat.le_of_dvd hrightPos (shiftedSquare_contentProduct_dvd P)
    _ ≤ P.minkowski.C₀ ^ 2 * 2 := Nat.mul_le_mul_left _ hbζ
    _ = 2 * P.minkowski.C₀ ^ 2 := by omega

/-- In particular, the source-coordinate content is at most the same
Minkowski scale. -/
theorem shiftedSquare_sourceContent_sq_le_two_mul_C₀_sq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.r ^ 2 ≤ 2 * P.minkowski.C₀ ^ 2 := by
  exact (Nat.le_mul_of_pos_right (P.r ^ 2) P.ell_pos).trans
    (shiftedSquare_contentProduct_le_two_mul_C₀_sq P)

/-- The primitive source norm scale is bounded below by the scale appearing
in the unbalanced determinant range. -/
theorem shiftedSquare_sourceNormScale_lower
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (shiftedSquareD₀ d : ℝ) / (2 * (P.minkowski.C₀ : ℝ)) ≤
      ((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
        (P.r : ℝ) ^ 2 := by
  have hC₀ : (0 : ℝ) < P.minkowski.C₀ := by
    exact_mod_cast P.minkowski.C₀_pos
  have hr : (0 : ℝ) < P.r := by
    exact_mod_cast P.r_pos
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * P.minkowski.C₀)
    (sq_pos_of_pos hr)).2
  have hnat :
      shiftedSquareD₀ d * P.r ^ 2 ≤
        (shiftedSquareD₀ d * P.minkowski.C₀) *
          (2 * P.minkowski.C₀) := by
    calc
      shiftedSquareD₀ d * P.r ^ 2 ≤
          shiftedSquareD₀ d * (2 * P.minkowski.C₀ ^ 2) :=
        Nat.mul_le_mul_left _
          (shiftedSquare_sourceContent_sq_le_two_mul_C₀_sq P)
      _ = (shiftedSquareD₀ d * P.minkowski.C₀) *
          (2 * P.minkowski.C₀) := by ring
  exact_mod_cast hnat

/-- The primitive target norm scale is at least the original target scale. -/
theorem shiftedSquare_targetNormScale_lower
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (w : ℝ) ≤
      ((w * P.minkowski.C₀ ^ 2 : ℕ) : ℝ) / (P.ell : ℝ) ^ 2 := by
  have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.ell_pos
  apply (le_div_iff₀ (sq_pos_of_pos hell)).2
  have hellC₀ : P.ell ≤ P.minkowski.C₀ :=
    Nat.le_of_dvd P.minkowski.C₀_pos P.ell_dvd_C₀
  have hnat : w * P.ell ^ 2 ≤ w * P.minkowski.C₀ ^ 2 :=
    Nat.mul_le_mul_left w (Nat.pow_le_pow_left hellC₀ 2)
  exact_mod_cast hnat

end

end PellPaper
