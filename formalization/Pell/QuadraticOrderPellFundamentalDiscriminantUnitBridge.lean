import Pell.QuadraticOrderPellFundamentalDiscriminantContainment
import Pell.QuadraticOrderPellSquarefreeUnitBridge

/-!
# Conditional power descent at a positive fundamental discriminant

The preceding containment theorem gives `2 * 𝓞_K ⊆ ℤ[√D]` in both branches of
`PositiveFundamentalDiscriminant`.  Consequently, if a power `u^j` of a
maximal-order unit is congruent to one modulo twice the maximal order, then
`u^(2j)` descends to the norm-one Pell subgroup.  In particular, a
finite-quotient calculation producing `j ∈ {1, 2, 3}` yields an exponent at
most six.

The congruence condition remains an assumption here.  It is the missing
finite quotient-of-units input for a full fundamental-unit comparison and is
not supplied by additive containment alone.
-/

namespace PellPaper

/-- If `u^j` is congruent to one modulo twice the maximal order at a positive
fundamental discriminant, then `u^(2j)` is an embedded norm-one Pell unit.
The exponent `j` is arbitrary; the intended finite-quotient input may later
bound it by three. -/
theorem quadraticOrderPellUnitEmbedding_pow_two_mul_mem_range_of_positiveFundamentalDiscriminant_pow_congruent_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ)
    (j : ℕ)
    (hu : ∃ x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      ((u ^ j : (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        1 + (2 : ℤ) • x) :
    u ^ (2 * j) ∈ Set.range (quadraticOrderPellUnitEmbedding (D : ℤ)) := by
  let O := NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))
  obtain ⟨x, hx⟩ := hu
  have hmem : ∃ z : ℤ√(D : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z =
        ((u ^ j : Oˣ) : O) := by
    obtain ⟨z, hz⟩ : ∃ z : ℤ√(D : ℤ),
        quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z = (2 : ℤ) • x :=
      quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_positiveFundamentalDiscriminant
        hD x
    refine ⟨1 + z, ?_⟩
    rw [map_add, map_one, hz]
    exact hx.symm
  have huinv : ∃ y : O,
      (((u ^ j : Oˣ)⁻¹ : Oˣ) : O) = 1 + (2 : ℤ) • y :=
    unit_inv_coe_eq_one_add_two_zsmul_of_coe_eq_one_add_two_zsmul
      (u ^ j : Oˣ) x hx
  obtain ⟨y, hy⟩ := huinv
  have hmeminv : ∃ z : ℤ√(D : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z =
        (((u ^ j : Oˣ)⁻¹ : Oˣ) : O) := by
    obtain ⟨z, hz⟩ : ∃ z : ℤ√(D : ℤ),
        quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z = (2 : ℤ) • y :=
      quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_positiveFundamentalDiscriminant
        hD y
    refine ⟨1 + z, ?_⟩
    rw [map_add, map_one, hz]
    exact hy.symm
  have hsq : (u ^ j) ^ 2 ∈ Set.range (quadraticOrderPellUnitEmbedding (D : ℤ)) :=
    quadraticOrderPellUnitEmbedding_square_mem_range_of_coe_and_inv_mem_range
      (D : ℤ) (u ^ j) hmem hmeminv
  simpa [pow_mul, Nat.mul_comm] using hsq

/-- Relative to a supplied fundamental Pell solution, the power-parametric
descent is a signed integral power of that solution's embedded unit. -/
theorem quadraticOrderPellUnitEmbedding_pow_two_mul_eq_zpow_or_neg_zpow_of_positiveFundamentalDiscriminant_pow_congruent_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a)
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ)
    (j : ℕ)
    (hu : ∃ x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      ((u ^ j : (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        1 + (2 : ℤ) • x) :
    ∃ n : ℤ,
      u ^ (2 * j) = (quadraticOrderPellUnitEmbedding (D : ℤ) a) ^ n ∨
      u ^ (2 * j) = -(quadraticOrderPellUnitEmbedding (D : ℤ) a) ^ n := by
  exact (mem_range_quadraticOrderPellUnitEmbedding_iff (D : ℤ) ha (u ^ (2 * j))).mp
    (quadraticOrderPellUnitEmbedding_pow_two_mul_mem_range_of_positiveFundamentalDiscriminant_pow_congruent_one
      D hD u j hu)

/-- The `j = 3` specialization of the power-parametric descent.  This is a
convenient consequence of a cube congruence, not a necessary form of the
finite-quotient input. -/
theorem quadraticOrderPellUnitEmbedding_pow_six_mem_range_of_positiveFundamentalDiscriminant_cube_congruent_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ)
    (hu : ∃ x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      ((u ^ 3 : (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        1 + (2 : ℤ) • x) :
    u ^ 6 ∈ Set.range (quadraticOrderPellUnitEmbedding (D : ℤ)) := by
  exact
    quadraticOrderPellUnitEmbedding_pow_two_mul_mem_range_of_positiveFundamentalDiscriminant_pow_congruent_one
      D hD u 3 hu

/-- The signed-power conclusion in the `j = 3` specialization. -/
theorem quadraticOrderPellUnitEmbedding_pow_six_eq_zpow_or_neg_zpow_of_positiveFundamentalDiscriminant_cube_congruent_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a)
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ)
    (hu : ∃ x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      ((u ^ 3 : (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        1 + (2 : ℤ) • x) :
    ∃ n : ℤ,
      u ^ 6 = (quadraticOrderPellUnitEmbedding (D : ℤ) a) ^ n ∨
      u ^ 6 = -(quadraticOrderPellUnitEmbedding (D : ℤ) a) ^ n := by
  exact
    quadraticOrderPellUnitEmbedding_pow_two_mul_eq_zpow_or_neg_zpow_of_positiveFundamentalDiscriminant_pow_congruent_one
      D hD ha u 3 hu

end PellPaper
