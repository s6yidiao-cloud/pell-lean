import Pell.ShiftedSquareMinkowskiC0Nu
import Pell.ShiftedSquareFieldDiscriminantBound

/-!
# The shifted-square Minkowski package with a radicand-scale bound

This module composes the frozen `C₀`--`nu` factorization candidate with the
reviewed quadratic field-discriminant bound.  It preserves the same witnesses,
exact norm identities, integral factorization, quotient-ideal identity, and
ideal containment, while replacing the field-discriminant bound on `C₀` by
the explicit manuscript-scale estimate

`C₀ ≤ 2 * sqrt |a|`.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareMinkowskiC₀NuAbsBound_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The project-facing shifted-square coordinate package.  All witnesses and
exact algebraic/ideal conclusions come from
`exists_shiftedSquareMinkowskiC₀Nu_package`; the only new step is the reviewed
uniform comparison `sqrt |discr K| ≤ 2 * sqrt |a|`. -/
theorem exists_shiftedSquareMinkowskiC₀Nu_package_abs_bound
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ (mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
        (C₀ : ℕ)
        (nu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
        (Q : Ideal (NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a)))),
      mu ∈ shiftedSquareIdealDivisor heq ∧
      mu ≠ 0 ∧
      0 < C₀ ∧
      |Algebra.norm ℚ (mu : rationalQuadraticAlgebra (-a))| =
        ((shiftedSquareD₀ d * C₀ : ℕ) : ℚ) ∧
      mu ^ 2 * nu =
        (C₀ : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) ^ 2 *
          shiftedSquareZetaInteger heq ∧
      Algebra.norm ℤ nu = ((w * C₀ ^ 2 : ℕ) : ℤ) ∧
      (C₀ : ℝ) ≤ 2 * Real.sqrt |a| ∧
      Ideal.span {mu} = shiftedSquareIdealDivisor heq * Q ∧
      Ideal.absNorm Q = C₀ ∧
      Ideal.span
          {(C₀ : NumberField.RingOfIntegers
            (rationalQuadraticAlgebra (-a)))} *
          shiftedSquareIdealDivisor heq ≤ Ideal.span {mu} := by
  obtain ⟨mu, C₀, nu, Q, hmu, hmu0, hC₀pos, hmuNorm,
      hfactor, hnuNorm, hC₀disc, hQ, hQnorm, hC₀I⟩ :=
    exists_shiftedSquareMinkowskiC₀Nu_package ha hd heq
  refine ⟨mu, C₀, nu, Q, hmu, hmu0, hC₀pos, hmuNorm,
    hfactor, hnuNorm, ?_, hQ, hQnorm, hC₀I⟩
  exact hC₀disc.trans
    (sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a)

end

end PellPaper
