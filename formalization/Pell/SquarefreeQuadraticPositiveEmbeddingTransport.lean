import Pell.SquarefreeQuadraticFundamentalUnitTransport

/-!
# Positive real embedding under squarefree fundamental transport

The explicit branchwise equivalence from a square-multiple radicand to its
positive fundamental presentation preserves the chosen positive real place.
This records the archimedean orientation needed when transporting unit-orbit
height estimates; it is stronger than an unoriented field-isomorphism claim.
-/

namespace PellPaper

open NumberField

noncomputable section

local instance squarefreePositiveEmbeddingTransport_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem squarefreeMulSqFundamentalAlgEquiv_omega_of_mod_four_eq_one
    (w s : ℕ) (hs : 0 < s) (hmod : w % 4 = 1) :
    squarefreeMulSqFundamentalAlgEquiv w s hs QuadraticAlgebra.omega =
      (⟨0, s⟩ : rationalQuadraticAlgebra
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ)) := by
  apply QuadraticAlgebra.ext <;>
    simp [squarefreeMulSqFundamentalAlgEquiv, hmod]

private theorem squarefreeMulSqFundamentalAlgEquiv_omega_of_mod_four_ne_one
    (w s : ℕ) (hs : 0 < s) (hmod : w % 4 ≠ 1) :
    squarefreeMulSqFundamentalAlgEquiv w s hs QuadraticAlgebra.omega =
      (⟨0, (s : ℚ) / 2⟩ : rationalQuadraticAlgebra
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ)) := by
  apply QuadraticAlgebra.ext <;>
    simp [squarefreeMulSqFundamentalAlgEquiv, hmod]

set_option backward.isDefEq.respectTransparency false in
/-- The explicit square-factor/fundamental-index equivalence intertwines the
chosen positive real embeddings. -/
theorem rationalQuadraticAlgebraRealEmbedding_comp_squarefreeMulSqFundamentalAlgEquiv
    (w s : ℕ) (hs : 0 < s) :
    (rationalQuadraticAlgebraRealEmbedding
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) (by positivity)).comp
      (squarefreeMulSqFundamentalAlgEquiv w s hs).toAlgHom =
    rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
      (by positivity) := by
  apply QuadraticAlgebra.algHom_ext
  by_cases hmod : w % 4 = 1
  · change rationalQuadraticAlgebraRealEmbedding
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) (by positivity)
        (squarefreeMulSqFundamentalAlgEquiv w s hs QuadraticAlgebra.omega) =
      rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
        (by positivity) QuadraticAlgebra.omega
    rw [squarefreeMulSqFundamentalAlgEquiv_omega_of_mod_four_eq_one
      w s hs hmod]
    simp [rationalQuadraticAlgebraRealEmbedding,
      squarefreeQuadraticFundamentalIndex, hmod]
    norm_num [Algebra.smul_def]
    ring
  · change rationalQuadraticAlgebraRealEmbedding
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) (by positivity)
        (squarefreeMulSqFundamentalAlgEquiv w s hs QuadraticAlgebra.omega) =
      rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
        (by positivity) QuadraticAlgebra.omega
    rw [squarefreeMulSqFundamentalAlgEquiv_omega_of_mod_four_ne_one
      w s hs hmod]
    simp [rationalQuadraticAlgebraRealEmbedding,
      squarefreeQuadraticFundamentalIndex, hmod]
    norm_num [Algebra.smul_def]
    ring

/-- Pointwise form of positive-real-embedding compatibility. -/
theorem rationalQuadraticAlgebraRealEmbedding_squarefreeMulSqFundamentalAlgEquiv
    (w s : ℕ) (hs : 0 < s)
    (z : rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ)) :
    rationalQuadraticAlgebraRealEmbedding
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) (by positivity)
        (squarefreeMulSqFundamentalAlgEquiv w s hs z) =
      rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
        (by positivity) z := by
  exact DFunLike.congr_fun
    (rationalQuadraticAlgebraRealEmbedding_comp_squarefreeMulSqFundamentalAlgEquiv
      w s hs) z

/-- The induced equivalence of rings of integers has the same compatibility
with the chosen positive real embeddings after coercion to the fields. -/
theorem rationalQuadraticAlgebraRealEmbedding_squarefreeMulSqFundamentalRingOfIntegersEquiv
    (w s : ℕ) (hs : 0 < s)
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ))]
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ))]
    (z : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) :
    rationalQuadraticAlgebraRealEmbedding
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) (by positivity)
        (((squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs z :
            NumberField.RingOfIntegers
              (rationalQuadraticAlgebra
                ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ))) :
          rationalQuadraticAlgebra
            ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ))) =
      rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
        (by positivity)
        ((z : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) :
          rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ)) := by
  change rationalQuadraticAlgebraRealEmbedding
      ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) (by positivity)
      (squarefreeMulSqFundamentalAlgEquiv w s hs
        ((z : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) :
          rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) = _
  exact rationalQuadraticAlgebraRealEmbedding_squarefreeMulSqFundamentalAlgEquiv
    w s hs _

end
end PellPaper
