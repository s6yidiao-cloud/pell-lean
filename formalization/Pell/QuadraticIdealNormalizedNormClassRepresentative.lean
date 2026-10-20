import Pell.QuadraticIdealNormalizedNormOrientation
import Pell.QuadraticIdealNormalizedNormScaleVectors
import Pell.IdealIntegerBasisPrincipalScale
import Pell.QuadraticFormIdealBasis
import Pell.QuadraticFormIdealClassMap
import Pell.QuadraticFormFundamentalPrimitive

/-!
# Every nonzero integral ideal has an attached form representative

Choose a negatively oriented actual integer ideal basis.  Its normalized
norm form has discriminant `D`, and fundamentality gives primitivity.
The proved integral vector identities give a nonzero principal scaling to
the actual attached ideal, hence equality of actual wide ideal classes.

This is a theorem for integral ideal representatives.  Quotient-level
surjectivity and class-number consequences are separate.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_normalizedNormClassRepresentative_numberField_instance
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- An actual nonzero ideal is principal-scaled to the actual ideal attached
to a primitive form of discriminant `D`; the right scalar is the ideal norm. -/
theorem exists_formAssociatedIdeal_principalScale_of_nonzeroIdeal
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
      (_hI : I ≠ ⊥), ∃ (Q : PrimitiveBinaryQuadraticForms (D : ℤ))
      (s : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      s ≠ 0 ∧ Ideal.span {s} * I =
        Ideal.span {(I.absNorm : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (D : ℤ)))} *
            formAssociatedIdeal (D : ℤ) Q.1 Q.2.2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro I hI
  obtain ⟨bI, hneg⟩ := exists_quadraticIdealIntegerBasis_negative_wedge D hD I hI
  have hQ := quadraticIdealNormalizedNormForm_discriminant_of_positiveFundamental
    D hD I hI bI
  let Q : PrimitiveBinaryQuadraticForms (D : ℤ) :=
    ⟨quadraticIdealNormalizedNormForm (D : ℤ) I bI,
      primitive_of_positiveFundamentalDiscriminant D hD _ hQ, hQ⟩
  let s := ringOfIntegersQuadraticConjugation (D : ℤ) (bI 0).1
  have hx : (bI 0).1 ≠ 0 := by
    intro hx
    apply bI.ne_zero 0
    exact Subtype.ext hx
  have hs : s ≠ 0 := by
    intro hs
    apply hx
    apply (ringOfIntegersQuadraticConjugation (D : ℤ)).injective
    simpa only [map_zero] using hs
  refine ⟨Q, s, hs, ?_⟩
  let bQ := formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant D hD Q
  apply ideal_principalScale_eq_of_integerBasis_scale I
    (formAssociatedIdeal (D : ℤ) Q.1 Q.2.2) bI bQ s I.absNorm
  have hvectors := quadraticIdealNormalizedNormForm_scale_vectors (D : ℤ) I bI hQ hneg
  intro i
  fin_cases i
  · change _ = (I.absNorm : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) *
      (formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant D hD Q 0 :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
    rw [formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant_zero]
    exact hvectors.1
  · change _ = (I.absNorm : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) *
      (formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant D hD Q 1 :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
    rw [formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant_one]
    exact hvectors.2

/-- Every nonzero actual integral ideal has the same actual wide ideal class
as the attached ideal of some primitive integral form of discriminant `D`. -/
theorem exists_formAssociatedIdealClass_eq_of_nonzeroIdeal
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
      (hI : I ≠ ⊥), ∃ Q : PrimitiveBinaryQuadraticForms (D : ℤ),
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q =
        idealClassOfNonzeroIdeal I hI := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro I hI
  obtain ⟨Q, s, hs, hscale⟩ :=
    exists_formAssociatedIdeal_principalScale_of_nonzeroIdeal D hD I hI
  have hnorm : (I.absNorm : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ))) ≠ 0 := by
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp hI)
  refine ⟨Q, ?_⟩
  have hJ := formAssociatedIdeal_ne_bot_of_a_ne_zero (D : ℤ) Q.1 Q.2.2
    (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q)
  exact (idealClassOfNonzeroIdeal_eq_of_principalScale I
    (formAssociatedIdeal (D : ℤ) Q.1 Q.2.2) hI hJ s I.absNorm hs hnorm hscale).symm

end
end IntegralBinaryQuadraticForm
end PellPaper
