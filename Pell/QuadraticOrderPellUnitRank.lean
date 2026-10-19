import Pell.QuadraticOrderPellRealTorsion
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Unit rank of the positive rational quadratic algebra

This module derives the rank-one conclusion from the explicit positive real
embedding and Mathlib's infinite-place signature formula.  It does not assume
that the field is totally real: the single constructed real embedding, together
with degree two, forces the signature.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- The positive real embedding, regarded as a complex embedding. -/
noncomputable def rationalQuadraticAlgebraComplexEmbedding (d : ℤ) (hd : 0 ≤ d) :
    rationalQuadraticAlgebra d →+* ℂ :=
  Complex.ofRealHom.comp (rationalQuadraticAlgebraRealEmbedding d hd).toRingHom

/-- The complex embedding induced by the positive real embedding is real. -/
theorem rationalQuadraticAlgebraComplexEmbedding_isReal
    (d : ℤ) (hd : 0 ≤ d)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField.ComplexEmbedding.IsReal
      (rationalQuadraticAlgebraComplexEmbedding d hd) := by
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext x
  simp [rationalQuadraticAlgebraComplexEmbedding,
    NumberField.ComplexEmbedding.conjugate_coe_eq]

/-- A nonnegative nonsquare rational quadratic algebra has at least one real
infinite place, supplied by its explicit positive real embedding. -/
theorem nrRealPlaces_pos_rationalQuadraticAlgebra
    (d : ℤ) (hd : 0 ≤ d)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    0 < NumberField.InfinitePlace.nrRealPlaces (rationalQuadraticAlgebra d) := by
  classical
  rw [← NumberField.InfinitePlace.card_real_embeddings]
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨rationalQuadraticAlgebraComplexEmbedding d hd,
    rationalQuadraticAlgebraComplexEmbedding_isReal d hd⟩⟩

/-- The rational quadratic algebra has degree two over `ℚ`. -/
theorem rationalQuadraticAlgebra_finrank_eq_two (d : ℤ) :
    Module.finrank ℚ (rationalQuadraticAlgebra d) = 2 := by
  exact QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

/-- A nonnegative nonsquare rational quadratic algebra has two real and no
complex infinite places.  This follows from degree two and the explicit real
embedding, rather than from a total-reality assumption. -/
theorem rationalQuadraticAlgebra_signature_of_nonneg
    (d : ℤ) (hd : 0 ≤ d)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField.InfinitePlace.nrRealPlaces (rationalQuadraticAlgebra d) = 2 ∧
      NumberField.InfinitePlace.nrComplexPlaces (rationalQuadraticAlgebra d) = 0 := by
  have hsignature := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
    (rationalQuadraticAlgebra d)
  have hreal := nrRealPlaces_pos_rationalQuadraticAlgebra d hd
  have hdegree := rationalQuadraticAlgebra_finrank_eq_two d
  omega

/-- The unit rank of a nonnegative nonsquare rational quadratic algebra is
one. -/
theorem quadraticOrderPellUnitRank_eq_one_of_nonneg
    (d : ℤ) (hd : 0 ≤ d)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField.Units.rank (rationalQuadraticAlgebra d) = 1 := by
  rw [NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  obtain ⟨hreal, hcomplex⟩ := rationalQuadraticAlgebra_signature_of_nonneg d hd
  omega

/-- Positive fundamental discriminants satisfy the hypotheses of the rank-one
statement. -/
theorem quadraticOrderPellUnitRank_eq_one_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.Units.rank (rationalQuadraticAlgebra (D : ℤ)) = 1 := by
  exact quadraticOrderPellUnitRank_eq_one_of_nonneg (D : ℤ)
    (int_pos_of_positiveFundamentalDiscriminant hD).le

end

end PellPaper
