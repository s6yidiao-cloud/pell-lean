import Pell.QuadraticOrderPellRingOfIntegers
import Mathlib.NumberTheory.Pell

/-!
# The norm-one Pell subgroup inside maximal-order units

For the concrete rational quadratic algebra already used in the project, this
module sends a norm-one Pell solution in the standard order `ℤ√d` to a unit of
the ring of integers of the associated quadratic field.  The map is induced by
the proved injective order embedding.

It embeds only the norm-one Pell subgroup.  In particular, it does not compare
this subgroup with all maximal-order units, prove a finite-index bound, choose
a positive fundamental unit, compare regulators, or prove a class-number
formula.
-/

namespace PellPaper

/-- The concrete embedding of norm-one Pell solutions in the standard
quadratic order into units of the associated maximal order. -/
noncomputable def quadraticOrderPellUnitEmbedding (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Pell.Solution₁ d →* (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ :=
  (Units.map (quadraticOrderPellEmbeddingToRingOfIntegers d).toMonoidHom).comp Unitary.toUnits

/-- Coercing the embedded unit to the ring of integers recovers the previously
constructed embedding of its underlying Pell-order element. -/
@[simp]
theorem coe_quadraticOrderPellUnitEmbedding (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] (a : Pell.Solution₁ d) :
    ((quadraticOrderPellUnitEmbedding d a :
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) =
      quadraticOrderPellEmbeddingToRingOfIntegers d (a : ℤ√d) :=
  rfl

/-- After both coercions, the embedded Pell unit agrees with the concrete
quadratic-algebra embedding. -/
@[simp]
theorem coe_coe_quadraticOrderPellUnitEmbedding (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] (a : Pell.Solution₁ d) :
    (((quadraticOrderPellUnitEmbedding d a :
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
          rationalQuadraticAlgebra d) =
      quadraticOrderPellEmbedding d (a : ℤ√d) :=
  rfl

/-- The Pell-unit embedding is injective. -/
theorem quadraticOrderPellUnitEmbedding_injective (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Function.Injective (quadraticOrderPellUnitEmbedding d) := by
  exact (Units.map_injective (quadraticOrderPellEmbeddingToRingOfIntegers_injective d)).comp
    Unitary.toUnits_injective

/-- At a positive fundamental-discriminant index, the preceding unit embedding
is available for the associated radicand.  The local `Fact` records precisely
the no-rational-root condition needed by the quadratic-algebra field instance. -/
noncomputable def quadraticOrderPellUnitEmbeddingAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    Pell.Solution₁ (D : ℤ) →*
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact quadraticOrderPellUnitEmbedding (D : ℤ)

/-- The positive-fundamental-discriminant specialization remains injective. -/
theorem quadraticOrderPellUnitEmbeddingAtPositiveFundamentalDiscriminant_injective
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    Function.Injective
      (quadraticOrderPellUnitEmbeddingAtPositiveFundamentalDiscriminant D hD) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact quadraticOrderPellUnitEmbedding_injective (D : ℤ)

end PellPaper
