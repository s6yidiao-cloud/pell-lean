import Pell.QuadraticFormWideClassProperTransform

/-!
# The proper-form quotient maps to the wide ideal class group

At a positive fundamental discriminant, the representative-level wide-class
invariance under proper transforms descends to the literal quotient
`ProperFormClass`.  This constructs only a map from proper form classes to the
actual *wide* ideal class group.  It makes no narrow-class assertion and no
injectivity, surjectivity, bijectivity, finiteness, cardinality, or
class-number claim.
-/

namespace PellPaper

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_properFormWideClass_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The representative-level map to the actual wide ideal class group descends
through proper equivalence.  The target is deliberately the wide class group;
this theorem does not identify its image or compare it with a narrow class
group. -/
noncomputable def properFormClassWideClassMapAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    ProperFormClass (D : ℤ) →
      let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
        ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
      ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  refine Quotient.lift
    (fun Q => formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q) ?_
  intro Q R hQR
  rcases hQR with ⟨g, hg⟩
  rw [← hg]
  exact formAssociatedIdealClassAtPositiveFundamentalDiscriminant_properTransformAt_eq
    D hD Q g

/-- Evaluating the descended map on the quotient class of a representative
recovers precisely that representative's attached wide ideal class. -/
theorem properFormClassWideClassMapAtPositiveFundamentalDiscriminant_apply_toProperFormClass
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD
        (PrimitiveBinaryQuadraticForms.toProperFormClass Q) =
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  rfl

end

end IntegralBinaryQuadraticForm

end PellPaper
