import Pell.QuadraticOrderPellUnitCyclic

/-!
# Coordinate and power-descent bridges for the Pell order

This file isolates two elementary pieces needed in a comparison between the
maximal order of a real quadratic field and the concrete Pell order
`ℤ[√d]`.

* The first theorem says exactly that twice an element of the rational
  quadratic algebra belongs to the Pell order precisely when both of its
  coordinates are half-integral.  Its ring-of-integers version is the
  elementwise form of the desired containment `2 * 𝓞_K ⊆ ℤ[√d]`; what
  remains elsewhere is to prove the stated coordinate integrality for all
  elements of the integral closure.
* The second theorem is a descent step for units.  Once a maximal-order unit
  and its inverse have a power in the Pell order, squaring that power has
  norm one and hence is an embedded Pell solution.  In particular, a
  cube-descent gives the exponent six occurring in the unit comparison.

No identification of the integral closure, finite quotient calculation, or
fundamental-unit comparison is asserted here.
-/

namespace PellPaper

/-- The two coordinates of `x` are half-integral.  This is the concrete
condition which makes `2 • x` lie in the standard Pell order. -/
def quadraticOrderPellHalfIntegralCoordinates (d : ℤ)
    (x : rationalQuadraticAlgebra d) : Prop :=
  ∃ a b : ℤ, (a : ℚ) = 2 * x.re ∧ (b : ℚ) = 2 * x.im

/-- Twice an element of the rational quadratic algebra lies in the concrete
Pell order exactly when its two coordinates are half-integral. -/
theorem quadraticOrderPellEmbedding_two_smul_mem_range_iff (d : ℤ)
    (x : rationalQuadraticAlgebra d) :
    (∃ z : ℤ√d, quadraticOrderPellEmbedding d z = (2 : ℚ) • x) ↔
      quadraticOrderPellHalfIntegralCoordinates d x := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.re, z.im, ?_, ?_⟩
    · have hre := congrArg QuadraticAlgebra.re hz
      simpa [quadraticOrderPellEmbedding_coordinates] using hre
    · have him := congrArg QuadraticAlgebra.im hz
      simpa [quadraticOrderPellEmbedding_coordinates] using him
  · rintro ⟨a, b, hre, him⟩
    refine ⟨Zsqrtd.mk a b, ?_⟩
    rw [quadraticOrderPellEmbedding_coordinates]
    ext <;> simp [hre, him]

/-- The ring-of-integers form of
`quadraticOrderPellEmbedding_two_smul_mem_range_iff`.  Thus a proof that
every algebraic integer has half-integral coordinates immediately yields the
elementwise containment `2 * 𝓞_K ⊆ ℤ[√d]`. -/
theorem quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_iff
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
    (∃ z : ℤ√d,
      quadraticOrderPellEmbeddingToRingOfIntegers d z = (2 : ℤ) • x) ↔
      quadraticOrderPellHalfIntegralCoordinates d
        (x : rationalQuadraticAlgebra d) := by
  constructor
  · rintro ⟨z, hz⟩
    apply
      (quadraticOrderPellEmbedding_two_smul_mem_range_iff d
        (x : rationalQuadraticAlgebra d)).mp
    refine ⟨z, ?_⟩
    have hcoe := congrArg
      (fun y : NumberField.RingOfIntegers (rationalQuadraticAlgebra d) =>
        (y : rationalQuadraticAlgebra d)) hz
    change quadraticOrderPellEmbedding d z = algebraMap _ _ ((2 : ℤ) • x) at hcoe
    rw [map_zsmul] at hcoe
    rw [hcoe]
    norm_num [Algebra.smul_def]
  · intro hx
    obtain ⟨z, hz⟩ : ∃ z : ℤ√d,
        quadraticOrderPellEmbedding d z =
          (2 : ℚ) • (x : rationalQuadraticAlgebra d) :=
      (quadraticOrderPellEmbedding_two_smul_mem_range_iff d
        (x : rationalQuadraticAlgebra d)).mpr hx
    refine ⟨z, ?_⟩
    apply NumberField.RingOfIntegers.ext
    change quadraticOrderPellEmbedding d z = algebraMap _ _ ((2 : ℤ) • x)
    rw [hz, map_zsmul]
    norm_num [Algebra.smul_def]

/-- If a maximal-order unit and its inverse both lie in the concrete Pell
order, then its square is represented by a norm-one Pell solution.  The
inverse hypothesis is essential: membership of a field unit in a nonmaximal
order alone does not yet give an inverse in that order. -/
theorem quadraticOrderPellUnitEmbedding_square_mem_range_of_coe_and_inv_mem_range
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ)
    (hu : ∃ z : ℤ√d,
      quadraticOrderPellEmbeddingToRingOfIntegers d z =
        (u : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)))
    (huinv : ∃ z : ℤ√d,
      quadraticOrderPellEmbeddingToRingOfIntegers d z =
        ((u⁻¹ : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d))) :
    u ^ 2 ∈ Set.range (quadraticOrderPellUnitEmbedding d) := by
  rcases hu with ⟨z, hz⟩
  rcases huinv with ⟨w, hw⟩
  have hzw : z * w = 1 := by
    apply quadraticOrderPellEmbeddingToRingOfIntegers_injective d
    rw [map_mul, hz, hw, (quadraticOrderPellEmbeddingToRingOfIntegers d).map_one]
    exact u.val_inv
  have hzunit : IsUnit z := isUnit_iff_exists_inv.mpr ⟨w, hzw⟩
  have hnorm : (z * z).norm = 1 := by
    have hnat : z.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hzunit
    rcases Int.natAbs_eq_iff.mp hnat with h | h
    · rw [Zsqrtd.norm_mul, h]
      norm_num
    · rw [Zsqrtd.norm_mul, h]
      norm_num
  let p : Pell.Solution₁ d :=
    ⟨z * z, Zsqrtd.norm_eq_one_iff_mem_unitary.mp hnorm⟩
  refine ⟨p, ?_⟩
  apply Units.ext
  change quadraticOrderPellEmbeddingToRingOfIntegers d (z * z) =
    (u : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) ^ 2
  rw [map_mul, hz]
  simp [pow_two]

/-- A cube of a maximal-order unit, together with its inverse, descending to
the concrete Pell order implies that the sixth power is an embedded
norm-one Pell solution.  This is the exact exponent-six handoff needed after
the finite quotient argument in the unit-comparison proof. -/
theorem quadraticOrderPellUnitEmbedding_pow_six_mem_range_of_cube_coe_and_inv_mem_range
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ)
    (hu : ∃ z : ℤ√d,
      quadraticOrderPellEmbeddingToRingOfIntegers d z =
        ((u ^ 3 : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d)))
    (huinv : ∃ z : ℤ√d,
      quadraticOrderPellEmbeddingToRingOfIntegers d z =
        (((u ^ 3)⁻¹ : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d))) :
    u ^ 6 ∈ Set.range (quadraticOrderPellUnitEmbedding d) := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul]
  exact quadraticOrderPellUnitEmbedding_square_mem_range_of_coe_and_inv_mem_range
    d (u ^ 3) hu huinv

end PellPaper
