import Pell.QuadraticFormIdealTransformCompatibility
import Pell.QuadraticFormIdealClassMap

/-!
# Proper transforms preserve the attached wide ideal class

For a primitive integral binary quadratic form of positive fundamental
discriminant, this module proves the two nonvanishing facts needed to turn the
explicit integral-ideal scaling relation into an equality in Mathlib's *wide*
ideal class group.  It remains deliberately below the quotient level: it does
not construct a map out of `ProperFormClass`, assert a narrow-class statement,
or prove any correspondence, bijection, finiteness, or class-number formula.
-/

namespace PellPaper

open scoped MatrixGroups

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formWideClass_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- For a primitive form at a positive fundamental discriminant, the explicit
factor in the proper-transform ideal scaling relation is nonzero.  This uses
the product identity for the two leading coefficients and the fact that both
the original and transformed primitive forms have nonzero leading coefficient. -/
theorem formProperTransformFactor_ne_zero_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) (g : SL(2, ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    formProperTransformFactor (D : ℤ) Q.1 Q.2.2 g ≠ 0 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have haQ : Q.1.a ≠ 0 :=
    leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q
  have haQg : (Q.1.properTransform g).a ≠ 0 := by
    simpa [properTransformAt] using
      (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD
        (properTransformAt Q g))
  intro hfactor
  have hprod :
      (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) *
          ((Q.1.properTransform g).a :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) = 0 := by
    rw [leadingCoefficient_mul_properTransformLeadingCoefficient_eq_factor_mul_companion
      (D : ℤ) Q.1 Q.2.2 g]
    rw [hfactor, zero_mul]
  have hcoeQ :
      (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) ≠ 0 := by
    exact_mod_cast haQ
  have hcoeQg :
      ((Q.1.properTransform g).a :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) ≠ 0 := by
    exact_mod_cast haQg
  exact (mul_ne_zero hcoeQ hcoeQg) hprod

/-- At a positive fundamental discriminant, the literal forms `Q` and
`Q.properTransformAt g` have equal images in the actual *wide* ideal class
group.  The proof uses exactly the explicit integral-ideal scaling equality;
it does not yet descend this statement through the proper-form quotient. -/
theorem formAssociatedIdealClassAtPositiveFundamentalDiscriminant_properTransformAt_eq
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) (g : SL(2, ℤ)) :
    formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q =
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD
        (properTransformAt Q g) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  have haQ : Q.1.a ≠ 0 :=
    leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q
  have haQg : (Q.1.properTransform g).a ≠ 0 := by
    simpa [properTransformAt] using
      (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD
        (properTransformAt Q g))
  have hfactor : formProperTransformFactor (D : ℤ) Q.1 Q.2.2 g ≠ 0 :=
    formProperTransformFactor_ne_zero_of_positiveFundamentalDiscriminant D hD Q g
  have hcoeQ :
      (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) ≠ 0 := by
    exact_mod_cast haQ
  have hclass := formAssociatedIdealClass_eq_of_principalScale
    (D : ℤ) Q.1 (Q.1.properTransform g) Q.2.2
    ((discriminant_properTransform Q.1 g).trans Q.2.2)
    haQ haQg
    (formProperTransformFactor (D : ℤ) Q.1 Q.2.2 g)
    (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
    hfactor hcoeQ
    (formAssociatedIdeal_principalScale_properTransform_eq (D : ℤ) Q.1 Q.2.2 g).symm
  simpa [formAssociatedIdealClassAtPositiveFundamentalDiscriminant,
    properTransformAt] using hclass

end

end IntegralBinaryQuadraticForm

end PellPaper
