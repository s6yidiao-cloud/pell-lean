import Pell.QuadraticOrderFormLatticeIndex
import Pell.QuadraticFormIdealTransformCompatibility
import Pell.QuadraticFormIdealClassMap

/-!
# A wide ideal-class map for primitive forms of any nonsquare discriminant

For an arbitrary integer discriminant whose rational quadratic algebra is a
field, every primitive form has a nonzero leading coefficient and hence an
actual attached ideal class.  The existing principal-scaling identity shows
that this class is invariant under `SL(2, ℤ)`, so it descends to the literal
proper-form quotient.

No positivity, fundamentality, description of the ring of integers, or
surjectivity/injectivity/cardinality assertion is used here.  The target is
the ordinary wide class group.
-/

namespace PellPaper

open scoped MatrixGroups

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_orderProperWideClass_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The actual wide ideal class attached to a primitive form of any
nonsquare discriminant. -/
noncomputable def primitiveFormAssociatedIdealClass (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (Q : PrimitiveBinaryQuadraticForms D) :
    ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
  formAssociatedIdealClass D Q.1 Q.2.2
    (leadingCoefficient_ne_zero_of_noRationalRoot D Q.1 Q.2.2)

/-- The explicit scaling factor for a proper transform is nonzero for every
form of nonsquare discriminant. -/
theorem formProperTransformFactor_ne_zero_of_noRationalRoot (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (Q : PrimitiveBinaryQuadraticForms D) (g : SL(2, ℤ)) :
    formProperTransformFactor D Q.1 Q.2.2 g ≠ 0 := by
  have haQ : Q.1.a ≠ 0 :=
    leadingCoefficient_ne_zero_of_noRationalRoot D Q.1 Q.2.2
  have hdiscQg : (Q.1.properTransform g).discriminant = D :=
    (discriminant_properTransform Q.1 g).trans Q.2.2
  have haQg : (Q.1.properTransform g).a ≠ 0 :=
    leadingCoefficient_ne_zero_of_noRationalRoot D (Q.1.properTransform g) hdiscQg
  intro hfactor
  have hprod :
      (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          ((Q.1.properTransform g).a :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = 0 := by
    rw [leadingCoefficient_mul_properTransformLeadingCoefficient_eq_factor_mul_companion
      D Q.1 Q.2.2 g]
    rw [hfactor, zero_mul]
  have hcoeQ :
      (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) ≠ 0 := by
    exact_mod_cast haQ
  have hcoeQg :
      ((Q.1.properTransform g).a :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) ≠ 0 := by
    exact_mod_cast haQg
  exact (mul_ne_zero hcoeQ hcoeQg) hprod

/-- Proper transformation preserves the actual attached wide ideal class at
every nonsquare discriminant. -/
theorem primitiveFormAssociatedIdealClass_properTransformAt_eq (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (Q : PrimitiveBinaryQuadraticForms D) (g : SL(2, ℤ)) :
    primitiveFormAssociatedIdealClass D Q =
      primitiveFormAssociatedIdealClass D (properTransformAt Q g) := by
  have haQ : Q.1.a ≠ 0 :=
    leadingCoefficient_ne_zero_of_noRationalRoot D Q.1 Q.2.2
  have hdiscQg : (Q.1.properTransform g).discriminant = D :=
    (discriminant_properTransform Q.1 g).trans Q.2.2
  have haQg : (Q.1.properTransform g).a ≠ 0 :=
    leadingCoefficient_ne_zero_of_noRationalRoot D (Q.1.properTransform g) hdiscQg
  have hfactor : formProperTransformFactor D Q.1 Q.2.2 g ≠ 0 :=
    formProperTransformFactor_ne_zero_of_noRationalRoot D Q g
  have hcoeQ :
      (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) ≠ 0 := by
    exact_mod_cast haQ
  have hclass := formAssociatedIdealClass_eq_of_principalScale
    D Q.1 (Q.1.properTransform g) Q.2.2 hdiscQg haQ haQg
    (formProperTransformFactor D Q.1 Q.2.2 g)
    (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    hfactor hcoeQ
    (formAssociatedIdeal_principalScale_properTransform_eq D Q.1 Q.2.2 g).symm
  simpa [primitiveFormAssociatedIdealClass, properTransformAt] using hclass

/-- The attached wide-class map on the literal proper-form quotient for any
nonsquare discriminant. -/
noncomputable def properFormClassWideClassMap (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ProperFormClass D →
      ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) := by
  refine Quotient.lift (primitiveFormAssociatedIdealClass D) ?_
  intro Q R hQR
  rcases hQR with ⟨g, hg⟩
  rw [← hg]
  exact primitiveFormAssociatedIdealClass_properTransformAt_eq D Q g

/-- Evaluation of the generic quotient map is exactly the attached ideal
class of the chosen primitive-form representative. -/
@[simp]
theorem properFormClassWideClassMap_apply_toProperFormClass (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (Q : PrimitiveBinaryQuadraticForms D) :
    properFormClassWideClassMap D
        (PrimitiveBinaryQuadraticForms.toProperFormClass Q) =
      primitiveFormAssociatedIdealClass D Q := rfl

end
end IntegralBinaryQuadraticForm
end PellPaper
