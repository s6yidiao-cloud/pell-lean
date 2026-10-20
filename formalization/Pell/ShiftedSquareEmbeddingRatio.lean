import Pell.ShiftedSquareSimultaneousNormalizedCoordinates
import Mathlib.Tactic

/-!
# Exact embedding-ratio identity for shifted squares

This isolated candidate proves the algebraic identity behind the local
ratio coordinates in the manuscript.  It first removes the positive coordinate
contents from the integral factorization and then conjugates that same
identity.  The cross-multiplied theorem avoids all division; a final theorem
records the literal quotient identity after deriving every required
nonvanishing fact from the coordinate package.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareEmbeddingRatio_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The integral factorization expressed using the two primitive coordinate
elements.  All scalar contents remain visible, so no cancellation is hidden
in this statement. -/
theorem shiftedSquare_primitiveCoordinate_factorization
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (((P.r : ℕ) : rationalQuadraticAlgebra (-a)) ^ 2 * P.ell) *
        ((shiftedSquareIntegralBasisElement P.basis P.x :
            rationalQuadraticAlgebra (-a)) ^ 2 *
          (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a))) =
      (P.minkowski.C₀ : rationalQuadraticAlgebra (-a)) ^ 2 *
        shiftedSquareZeta a d n := by
  have h := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)) =>
      (z : rationalQuadraticAlgebra (-a)))
    P.minkowski.factorization
  rw [P.mu_coordinates, P.nu_coordinates] at h
  norm_num at h ⊢
  ring_nf at h ⊢
  exact h

/-- Quadratic conjugation of the primitive-coordinate factorization. -/
theorem shiftedSquare_primitiveCoordinate_conjugate_factorization
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (((P.r : ℕ) : rationalQuadraticAlgebra (-a)) ^ 2 * P.ell) *
        (star (shiftedSquareIntegralBasisElement P.basis P.x :
            rationalQuadraticAlgebra (-a)) ^ 2 *
          star (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a))) =
      (P.minkowski.C₀ : rationalQuadraticAlgebra (-a)) ^ 2 *
        star (shiftedSquareZeta a d n) := by
  have h := congrArg star
    (shiftedSquare_primitiveCoordinate_factorization P)
  simpa only [star_mul', star_pow, star_natCast] using h

/-- Cross-multiplied form of
`rho_alpha⁻² * rho_gamma = conjugate(zeta) / zeta`.
This is the denominator-free invariant actually needed to justify the local
ratio map. -/
theorem shiftedSquare_embeddingRatio_crossIdentity
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    star (shiftedSquareIntegralBasisElement P.basis P.x :
        rationalQuadraticAlgebra (-a)) ^ 2 *
        star (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a)) *
        shiftedSquareZeta a d n =
      (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a)) ^ 2 *
        (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a)) *
        star (shiftedSquareZeta a d n) := by
  let S : rationalQuadraticAlgebra (-a) :=
    ((P.r : ℕ) : rationalQuadraticAlgebra (-a)) ^ 2 * P.ell
  let T : rationalQuadraticAlgebra (-a) :=
    (P.minkowski.C₀ : rationalQuadraticAlgebra (-a)) ^ 2
  let alpha : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.x
  let gamma : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.y
  let zeta : rationalQuadraticAlgebra (-a) := shiftedSquareZeta a d n
  have hS : S ≠ 0 := by
    dsimp only [S]
    exact mul_ne_zero
      (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.r_pos)))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.ell_pos))
  have hT : T ≠ 0 := by
    dsimp only [T]
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.minkowski.C₀_pos))
  have hfactor : S * (alpha ^ 2 * gamma) = T * zeta := by
    simpa only [S, T, alpha, gamma, zeta] using
      shiftedSquare_primitiveCoordinate_factorization P
  have hfactorStar : S * (star alpha ^ 2 * star gamma) = T * star zeta := by
    simpa only [S, T, alpha, gamma, zeta] using
      shiftedSquare_primitiveCoordinate_conjugate_factorization P
  apply mul_left_cancel₀ (mul_ne_zero hS hT)
  calc
    S * T * (star alpha ^ 2 * star gamma * zeta) =
        (S * (star alpha ^ 2 * star gamma)) * (T * zeta) := by ring
    _ = (T * star zeta) * (S * (alpha ^ 2 * gamma)) := by
      rw [hfactorStar, hfactor]
    _ = S * T * (alpha ^ 2 * gamma * star zeta) := by ring

/-- Literal quotient form of the manuscript's invariant square map.  The
source and target elements, their conjugates, and `zeta` are all proved
nonzero from the same coordinate package before denominators are cleared. -/
theorem shiftedSquare_embeddingRatio_identity
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ((shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a)) /
        star (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a)))⁻¹ ^ 2 *
        (star (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a)) /
          (shiftedSquareIntegralBasisElement P.basis P.y :
            rationalQuadraticAlgebra (-a))) =
      star (shiftedSquareZeta a d n) / shiftedSquareZeta a d n := by
  let alpha : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.x
  let gamma : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.y
  let zeta : rationalQuadraticAlgebra (-a) := shiftedSquareZeta a d n
  have halpha : alpha ≠ 0 := by
    intro hzero
    have hxzero : shiftedSquareIntegralBasisElement P.basis P.x = 0 := by
      apply Subtype.ext
      exact hzero
    apply P.minkowski.mu_ne_zero
    rw [P.mu_coordinates, hxzero, smul_zero]
  have hgamma : gamma ≠ 0 := by
    intro hzero
    have hyzero : shiftedSquareIntegralBasisElement P.basis P.y = 0 := by
      apply Subtype.ext
      exact hzero
    apply P.nu_ne_zero
    rw [P.nu_coordinates, hyzero, smul_zero]
  have hzeta : zeta ≠ 0 := by
    intro hzero
    have hfactor := shiftedSquare_primitiveCoordinate_factorization P
    rw [show shiftedSquareZeta a d n = 0 from hzero] at hfactor
    have hS :
        (((P.r : ℕ) : rationalQuadraticAlgebra (-a)) ^ 2 * P.ell) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.r_pos)))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.ell_pos))
    have hleft :
        (((P.r : ℕ) : rationalQuadraticAlgebra (-a)) ^ 2 * P.ell) *
            (alpha ^ 2 * gamma) ≠ 0 :=
      mul_ne_zero hS (mul_ne_zero (pow_ne_zero 2 halpha) hgamma)
    have hfactorZero :
        (((P.r : ℕ) : rationalQuadraticAlgebra (-a)) ^ 2 * P.ell) *
            (alpha ^ 2 * gamma) = 0 := by
      simpa only [alpha, gamma, hzero, mul_zero] using hfactor
    exact hleft hfactorZero
  have hcross := shiftedSquare_embeddingRatio_crossIdentity P
  change (alpha / star alpha)⁻¹ ^ 2 * (star gamma / gamma) =
    star zeta / zeta
  rw [inv_div]
  have hrearrange :
      (star alpha / alpha) ^ 2 * (star gamma / gamma) =
        (star alpha ^ 2 * star gamma) / (alpha ^ 2 * gamma) := by
    field_simp [halpha, hgamma]
  rw [hrearrange]
  apply (div_eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 halpha) hgamma) hzeta).2
  simpa only [alpha, gamma, zeta, mul_assoc, mul_comm, mul_left_comm] using hcross

end

end PellPaper
