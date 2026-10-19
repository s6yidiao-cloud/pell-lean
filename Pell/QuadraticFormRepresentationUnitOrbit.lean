import Pell.QuadraticFormRepresentationIdeal
import Pell.QuadraticOrderPellFundamentalUnitModel

/-!
# The signed unit orbit inside one representation-ideal fibre

If two vectors represent the same nonzero value of a quadratic form and have
the same quotient ideal, their form-ideal vectors differ by a unit.  Taking
the algebra norm and using equality of the represented values forces that
unit to have norm `+1`.  The unit group of a positive real quadratic field has
rank one and torsion `{1,-1}`, so the unit is a signed integral power of the
sole fundamental-system generator.

This is the algebraic orbit classification compressed into
the manuscript.  The generator used here is not yet oriented at the
positive real place; the archimedean height-window count remains separate.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance representationUnitOrbit_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Equal nonzero represented values in one quotient-ideal fibre differ by a
norm-one unit, which is a signed power of the rank-one fundamental-system
generator. -/
theorem exists_norm_one_signed_rankOneFundamentalUnit_orbit
    (D : ℤ) (hD : 0 ≤ D)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    {x₁ y₁ x₂ y₂ : ℤ}
    (ha : Q.a ≠ 0)
    (hvalue : Q.eval x₁ y₁ = Q.eval x₂ y₂)
    (hvalue0 : Q.eval x₁ y₁ ≠ 0)
    (hJ : formRepresentationQuotientIdeal D Q hQ x₁ y₁ =
      formRepresentationQuotientIdeal D Q hQ x₂ y₂) :
    let g := rankOneFundamentalUnit (rationalQuadraticAlgebra D)
      (quadraticOrderPellUnitRank_eq_one_of_nonneg D hD)
    ∃ (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))ˣ)
      (n : ℤ),
      Algebra.norm ℤ
          (u : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = 1 ∧
      formIdealVector D Q hQ x₁ y₁ *
          (u : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
        formIdealVector D Q hQ x₂ y₂ ∧
      (u = g ^ n ∨ u = -(g ^ n)) := by
  dsimp only
  obtain ⟨u, hu⟩ :=
    associated_formIdealVector_of_formRepresentationQuotientIdeal_eq
      D Q hQ hJ
  have hnorm := congrArg (Algebra.norm ℤ) hu
  rw [map_mul, algebraNorm_formIdealVector D Q hQ,
    algebraNorm_formIdealVector D Q hQ, ← hvalue] at hnorm
  have hunorm : Algebra.norm ℤ
      (u : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra D)) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero ha hvalue0)
    simpa only [mul_one] using hnorm
  obtain ⟨n, hn⟩ := rankOneFundamentalUnit_signed_zpow
    (rationalQuadraticAlgebra D)
    (quadraticOrderPellUnitRank_eq_one_of_nonneg D hD)
    (fun z hz => by
      apply quadraticOrderPellUnit_eq_one_or_neg_one_of_mem_torsion
        D hD z
      simpa [NumberField.Units.torsion] using hz)
    u
  exact ⟨u, n, hunorm, hu, hn⟩

end
end IntegralBinaryQuadraticForm
end PellPaper
