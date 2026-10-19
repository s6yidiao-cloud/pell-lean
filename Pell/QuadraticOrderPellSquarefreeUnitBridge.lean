import Pell.QuadraticOrderPellTraceNorm

/-!
# Squarefree order containment to Pell-unit descent

For a squarefree radicand, `QuadraticOrderPellTraceNorm` proves the
elementwise containment `2 * 𝓞_K ⊆ ℤ[√D]`.  This module records the convenient
specialization in which the remaining finite-quotient input is

`u³ ≡ 1 (mod 2 * 𝓞_K)`.

It then produces an actual norm-one Pell unit: `u⁶` belongs to the embedded
Pell subgroup.  The inverse congruence is derived algebraically, so only the
forward congruence is assumed.  A full quotient calculation need not take
this cube form; it may instead produce another controlled exponent.
-/

namespace PellPaper

/-- A unit congruent to one modulo twice the ambient ring has an inverse with
the same form.  This elementary fact removes a redundant inverse hypothesis
from the squarefree unit descent. -/
theorem unit_inv_coe_eq_one_add_two_zsmul_of_coe_eq_one_add_two_zsmul
    {R : Type*} [CommRing R] (u : Rˣ) (x : R)
    (hu : (u : R) = 1 + (2 : ℤ) • x) :
    ∃ y : R, ((u⁻¹ : Rˣ) : R) = 1 + (2 : ℤ) • y := by
  let v : R := ((u⁻¹ : Rˣ) : R)
  refine ⟨-v * x, ?_⟩
  have hmul : v * (u : R) = 1 := by
    dsimp [v]
    change u.inv * (u : R) = 1
    exact u.inv_val
  rw [hu] at hmul
  change v = 1 + (2 : ℤ) • (-v * x)
  simp only [two_zsmul, mul_add, mul_one, neg_mul] at hmul ⊢
  have htarget : v = 1 + (-(v * x) + -(v * x)) := by
    calc
      v = (v + (v * x + v * x)) - (v * x + v * x) := by abel
      _ = 1 - (v * x + v * x) := by rw [hmul]
      _ = 1 + (-(v * x) + -(v * x)) := by abel
  simpa [neg_mul] using htarget

/-- The `j = 3` specialization: if a maximal-order unit has cube congruent to
one modulo twice the ring of integers in the squarefree branch, then its
sixth power is an embedded norm-one Pell solution. -/
theorem quadraticOrderPellUnitEmbedding_pow_six_mem_range_of_squarefree_cube_congruent_one
    (D : ℕ) (hD : Squarefree D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ)
    (hu : ∃ x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      ((u ^ 3 : (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        1 + (2 : ℤ) • x) :
    u ^ 6 ∈ Set.range (quadraticOrderPellUnitEmbedding (D : ℤ)) := by
  let O := NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))
  obtain ⟨x, hx⟩ := hu
  have hmem : ∃ z : ℤ√(D : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z =
        ((u ^ 3 : Oˣ) : O) := by
    obtain ⟨z, hz⟩ : ∃ z : ℤ√(D : ℤ),
        quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z = (2 : ℤ) • x :=
      quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_squarefree
        D hD x
    refine ⟨1 + z, ?_⟩
    rw [map_add, map_one, hz]
    exact hx.symm
  have huinv : ∃ y : O,
      (((u ^ 3 : Oˣ)⁻¹ : Oˣ) : O) = 1 + (2 : ℤ) • y :=
    unit_inv_coe_eq_one_add_two_zsmul_of_coe_eq_one_add_two_zsmul
      (u ^ 3 : Oˣ) x hx
  obtain ⟨y, hy⟩ := huinv
  have hmeminv : ∃ z : ℤ√(D : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z =
        (((u ^ 3 : Oˣ)⁻¹ : Oˣ) : O) := by
    obtain ⟨z, hz⟩ : ∃ z : ℤ√(D : ℤ),
        quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z = (2 : ℤ) • y :=
      quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_squarefree
        D hD y
    refine ⟨1 + z, ?_⟩
    rw [map_add, map_one, hz]
    exact hy.symm
  exact quadraticOrderPellUnitEmbedding_pow_six_mem_range_of_cube_coe_and_inv_mem_range
    (D : ℤ) u hmem hmeminv

/-- Relative to any supplied fundamental Pell solution, the descended sixth
power is a signed integral power of its embedded Pell unit. -/
theorem quadraticOrderPellUnitEmbedding_pow_six_eq_zpow_or_neg_zpow_of_squarefree_cube_congruent_one
    (D : ℕ) (hD : Squarefree D)
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
  exact (mem_range_quadraticOrderPellUnitEmbedding_iff (D : ℤ) ha (u ^ 6)).mp
    (quadraticOrderPellUnitEmbedding_pow_six_mem_range_of_squarefree_cube_congruent_one
      D hD u hu)

end PellPaper
