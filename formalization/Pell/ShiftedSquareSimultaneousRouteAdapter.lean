import Pell.ShiftedSquareCoordinateFiber
import Pell.ShiftedSquareExplicitIntegralBasisHeight
import Pell.ShiftedSquareSimultaneousNormalizedCoordinates
import Mathlib.Tactic

/-!
# Route adapters for simultaneous shifted-square coordinates

This isolated candidate connects the simultaneous normalized package to the
exact fixed-coordinate fibre and to the uniform six-coefficient height bound.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareSimultaneousRouteAdapter_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- A simultaneous normalized package supplies an inhabitant of its exact
fixed-coordinate fibre. -/
def ShiftedSquareSimultaneousNormalizedCoordinatePackage.toFixedCoordinateSolution
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ShiftedSquareFixedCoordinateSolution a P.basis P.t P.c
      P.minkowski.C₀ P.r P.ell P.x P.y where
  d := d
  w := w
  n := n
  equation := heq
  factorization := by
    rw [← P.mu_coordinates, ← P.nu_coordinates]
    exact P.minkowski.factorization
  source_norm := P.mu_norm_form
  target_norm := P.nu_norm_form

/-- The basis parameter in a simultaneous normalized package gives a surface
coefficient height linear in the absolute field parameter. -/
theorem ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceCoefficientHeight_le
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    shiftedSquareSurfaceCoefficientHeight P.c ≤ 8 * a.natAbs + 4 :=
  shiftedSquareSurfaceCoefficientHeight_le_eight_mul_natAbs_add_four
    P.basis P.omega P.t P.c P.basis_zero P.basis_one
      P.t_zero_or_one P.omega_sq

/-- Every entry of the explicit surface tensor is bounded directly by the
field-parameter height. -/
theorem ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceCoefficient_abs_le
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (i : Fin 3) (j : Fin 2) :
    |shiftedSquareSurfaceCoefficients P.t P.c i j| ≤
      ((8 * a.natAbs + 4 : ℕ) : ℤ) := by
  calc
    |shiftedSquareSurfaceCoefficients P.t P.c i j| ≤
        (shiftedSquareSurfaceCoefficientHeight P.c : ℤ) :=
      abs_shiftedSquareSurfaceCoefficients_le_height
        P.t P.c P.t_zero_or_one i j
    _ ≤ ((8 * a.natAbs + 4 : ℕ) : ℤ) := by
      exact_mod_cast P.surfaceCoefficientHeight_le

/-- Any finite collection of original triples with this exact package data
has cardinality at most one. -/
theorem ShiftedSquareSimultaneousNormalizedCoordinatePackage.fixedFiber_card_le_one
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (S : Finset (ShiftedSquareFixedCoordinateSolution a P.basis P.t P.c
      P.minkowski.C₀ P.r P.ell P.x P.y)) :
    S.card ≤ 1 :=
  card_shiftedSquareFixedCoordinateSolution_le_one P.minkowski.C₀_pos S

end

end PellPaper
