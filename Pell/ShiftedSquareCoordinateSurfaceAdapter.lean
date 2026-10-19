import Pell.ShiftedSquareMinkowskiCoordinates
import Pell.TwoLayerCommonFactorSelection

/-!
# The shifted-square coordinate surface in the generic two-layer interface

This module freezes the convention by which the primitive Minkowski
coordinates enter the repository's generic bidegree-`(2,1)` eliminant and
projection machinery.  The source vector is `x`, the target vector is `y`,
and neither pair is reversed.

No determinant estimate, coefficient-height bound, square-sieve estimate, or
count for shifted-square blocks is asserted here.
-/

namespace PellPaper

noncomputable section

/-- The literal no-reversal conversion from source and target coordinate
vectors to the point convention used by two-layer auxiliary forms. -/
def shiftedSquareCoordinatePoint (x y : Fin 2 → ℤ) : TwoLayerFormPoint :=
  ((x 0, x 1), (y 0, y 1))

/-- The exact surface payload of a primitive Minkowski coordinate package.
The equation is oriented as required by the generic eliminant API. -/
theorem shiftedSquareMinkowskiPrimitiveCoordinatePackage_surfaceData
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareMinkowskiPrimitiveCoordinatePackage heq) :
    IsCoprime (P.x 0) (P.x 1) ∧
      IsCoprime (P.y 0) (P.y 1) ∧
      P.level ≠ 0 ∧
      quadraticLinearFormEval
          (shiftedSquareIntegralBasisQuadraticLinearCoefficients
            P.basis P.selectedCoordinate) P.x P.y = P.level ∧
      (P.r : ℤ) ^ 2 *
          |shiftedSquareIntegralBasisNormEval P.basis P.x| =
        ((shiftedSquareD₀ d * P.C₀ : ℕ) : ℤ) ∧
      (P.ell : ℤ) ^ 2 *
          shiftedSquareIntegralBasisNormEval P.basis P.y =
        ((w * P.C₀ ^ 2 : ℕ) : ℤ) ∧
      ((P.r : ℤ) ^ 2 * (P.ell : ℤ)) * P.level =
        (P.C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates P.basis
            (shiftedSquareZetaInteger heq) P.selectedCoordinate ∧
      ((P.r : ℤ) ^ 2 * (P.ell : ℤ)) ∣
        (P.C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates P.basis
            (shiftedSquareZetaInteger heq) P.selectedCoordinate := by
  exact ⟨P.x_primitive, P.y_primitive, P.level_ne_zero, P.level_eq.symm,
    P.mu_primitive_norm, P.nu_primitive_norm,
    P.selected_coordinate_relation, P.content_dvd_selected_zeta_level⟩

/-- A finite shifted-coordinate cell enters the existing common-factor and
eliminant-square projection theorem with source `x` and target `y` in exactly
that order.  All factor data remain explicit hypotheses and both counting
branches remain in the conclusion. -/
theorem card_shiftedSquareCoordinateSurface_le_targetFactorZeros_add_twiceSquares
    (n b : ℕ) (f : twoLayerFormIndex n → ℤ)
    (f' : twoLayerFormIndex b → ℤ) (D : MvPolynomial (Fin 2) ℤ)
    (hfactor : ∀ i : Fin 2, twoLayerBinaryPolynomial n f i =
      D * twoLayerBinaryPolynomial b f' i)
    (hcomponents : ∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
      MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 0) ≠ 0 ∨
        MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 1) ≠ 0)
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (hc : c ≠ 0)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (T : Finset (Fin 2 → ℤ))
    (hsource : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1))
    (htarget : ∀ p ∈ S, IsCoprime (p.2 0) (p.2 1))
    (haux : ∀ p ∈ S,
      twoLayerFormEval n f (shiftedSquareCoordinatePoint p.1 p.2) = 0)
    (hsurface : ∀ p ∈ S, quadraticLinearFormEval g p.1 p.2 = c)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ (S.filter fun p => MvPolynomial.eval p.2 D = 0).card +
      2 * (T.filter fun y =>
        IsSquare (MvPolynomial.eval y (twoLayerEliminant b f' g c)) ∧
          MvPolynomial.eval y (twoLayerEliminant b f' g c) ≠ 0).card := by
  apply card_twoLayer_solutions_le_target_factor_zeros_add_twice_squares
    n b f f' D hfactor hcomponents g c hc S T
  · intro p hp
    refine ⟨hsource p hp, htarget p hp, ?_, hsurface p hp⟩
    simpa only [shiftedSquareCoordinatePoint] using haux p hp
  · exact hT

end

end PellPaper
