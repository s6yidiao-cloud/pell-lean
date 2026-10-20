import Pell.QuadraticOrderPellTraceNorm
import Pell.QuadraticOrderPellFourRadicandContainment

/-!
# The Pell order contains twice the maximal order at a fundamental discriminant

The two arithmetic shapes in `PositiveFundamentalDiscriminant` have separate
coordinate proofs: a squarefree radicand, and a radicand of the form `4d` with
`d ≡ 2, 3 (mod 4)`.  This module combines them into the single containment
needed when comparing the concrete Pell order with the maximal order.

It proves only the additive containment `2 * 𝓞_K ⊆ ℤ[√D]`.  In particular it
does not calculate the quotient of unit groups or assert an exponent for it.
-/

namespace PellPaper

/-- At every positive fundamental discriminant, twice each algebraic integer
of the rational quadratic field lies in the concrete Pell order. -/
theorem quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_positiveFundamentalDiscriminant
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
    ∃ z : ℤ√(D : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z = (2 : ℤ) • x := by
  rcases hD.2 with hsq | hfour
  · exact quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_squarefree
      D hsq.1 x
  · rcases hfour with ⟨d, hD, hdsq, hdmod⟩
    subst D
    exact
      quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_nat_four_mul_squarefree_mod_four
        d hdsq hdmod x

end PellPaper
