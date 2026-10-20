import Pell.QuadraticOrderPellUnitEmbedding
import Mathlib.NumberTheory.Pell

/-!
# Signed-power structure of the embedded norm-one Pell subgroup

For a supplied fundamental solution, Mathlib proves that every norm-one Pell
solution is a signed integral power of it.  This module transports that exact
statement through the injective embedding of the standard Pell order into the
units of the maximal order.

The result concerns only the image of `Pell.Solution₁ d`.  It neither identifies
that image with all maximal-order units nor proves an index, a positivity
statement, or a regulator/fundamental-unit comparison.
-/

namespace PellPaper

/-- The Pell-unit embedding preserves integral powers. -/
@[simp]
theorem quadraticOrderPellUnitEmbedding_zpow (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (a : Pell.Solution₁ d) (n : ℤ) :
    quadraticOrderPellUnitEmbedding d (a ^ n) =
      (quadraticOrderPellUnitEmbedding d a) ^ n := by
  exact (quadraticOrderPellUnitEmbedding d).map_zpow a n

/-- The Pell-unit embedding preserves the sign of a Pell solution. -/
@[simp]
theorem quadraticOrderPellUnitEmbedding_neg (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (a : Pell.Solution₁ d) :
    quadraticOrderPellUnitEmbedding d (-a) =
      -quadraticOrderPellUnitEmbedding d a := by
  apply Units.ext
  change quadraticOrderPellEmbeddingToRingOfIntegers d
      ((-a : Pell.Solution₁ d) : ℤ√d) = _
  rw [show ((-a : Pell.Solution₁ d) : ℤ√d) = -(a : ℤ√d) by rfl]
  simp

/-- The signed power formula after embedding a Pell solution into maximal-order
units. -/
@[simp]
theorem quadraticOrderPellUnitEmbedding_neg_zpow (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (a : Pell.Solution₁ d) (n : ℤ) :
    quadraticOrderPellUnitEmbedding d (-(a ^ n)) =
      -(quadraticOrderPellUnitEmbedding d a) ^ n := by
  rw [quadraticOrderPellUnitEmbedding_neg,
    quadraticOrderPellUnitEmbedding_zpow]

/-- Every embedded norm-one Pell solution is, up to sign, an integral power of
the embedded supplied fundamental Pell solution. -/
theorem quadraticOrderPellUnitEmbedding_eq_zpow_or_neg_zpow (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) (b : Pell.Solution₁ d) :
    ∃ n : ℤ,
      quadraticOrderPellUnitEmbedding d b =
        (quadraticOrderPellUnitEmbedding d a) ^ n ∨
      quadraticOrderPellUnitEmbedding d b =
        -(quadraticOrderPellUnitEmbedding d a) ^ n := by
  obtain ⟨n, hb | hb⟩ := ha.eq_zpow_or_neg_zpow b
  · refine ⟨n, Or.inl ?_⟩
    rw [hb]
    exact quadraticOrderPellUnitEmbedding_zpow d a n
  · refine ⟨n, Or.inr ?_⟩
    rw [hb]
    exact quadraticOrderPellUnitEmbedding_neg_zpow d a n

/-- Exact image formulation of the signed-power description: membership in the
embedded norm-one Pell subgroup is equivalent to being a signed integral power
of the embedded fundamental Pell solution.  Thus this is a cyclic description
only after quotienting by the sign subgroup; it does not assert that the full
Pell subgroup itself is cyclic. -/
theorem mem_range_quadraticOrderPellUnitEmbedding_iff (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a)
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
    u ∈ Set.range (quadraticOrderPellUnitEmbedding d) ↔
      ∃ n : ℤ,
        u = (quadraticOrderPellUnitEmbedding d a) ^ n ∨
        u = -(quadraticOrderPellUnitEmbedding d a) ^ n := by
  constructor
  · rintro ⟨b, rfl⟩
    exact quadraticOrderPellUnitEmbedding_eq_zpow_or_neg_zpow d ha b
  · rintro ⟨n, hu | hu⟩
    · refine ⟨a ^ n, ?_⟩
      rw [quadraticOrderPellUnitEmbedding_zpow]
      exact hu.symm
    · refine ⟨-(a ^ n), ?_⟩
      rw [quadraticOrderPellUnitEmbedding_neg_zpow]
      exact hu.symm

end PellPaper
