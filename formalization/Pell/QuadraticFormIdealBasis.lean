import Pell.QuadraticFormIdealIntegerCoordinates
import Pell.QuadraticFormIdealVectorNorm
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# The integer basis of an attached form ideal

At a positive fundamental discriminant, the checked integer-coordinate
description gives an explicit linear equivalence from `Fin 2 → ℤ` onto the
actual attached ideal.  Its standard basis vectors are `a` and `-theta`.
No span or index assumption is introduced.  This module makes no claim
about fibres of the map from proper form classes to wide ideal classes.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdealBasis_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Send the two integer coordinates to the vector `a*x - theta*y` in the
actual attached ideal. -/
def formAssociatedIdealIntegerLinearMap
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Fin 2 → ℤ) →ₗ[ℤ] formAssociatedIdeal D Q hQ where
  toFun v := ⟨formIdealVector D Q hQ (v 0) (v 1), formIdealVector_mem D Q hQ (v 0) (v 1)⟩
  map_add' v w := by
    apply Subtype.ext
    change formIdealVector D Q hQ (v 0 + w 0) (v 1 + w 1) =
      formIdealVector D Q hQ (v 0) (v 1) + formIdealVector D Q hQ (w 0) (w 1)
    simp only [formIdealVector, Int.cast_add]
    ring
  map_smul' n v := by
    apply Subtype.ext
    change formIdealVector D Q hQ (n * v 0) (n * v 1) =
      n • formIdealVector D Q hQ (v 0) (v 1)
    simp only [formIdealVector, Int.cast_mul, zsmul_eq_mul]
    ring

/-- The forward linear map has exactly the prescribed coordinate formula. -/
@[simp]
theorem coe_formAssociatedIdealIntegerLinearMap
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (v : Fin 2 → ℤ) :
    (formAssociatedIdealIntegerLinearMap D Q hQ v :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
      formIdealVector D Q hQ (v 0) (v 1) := rfl

/-- Nonzero leading coefficient makes the coordinate linear map injective. -/
theorem formAssociatedIdealIntegerLinearMap_injective
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (ha : Q.a ≠ 0) :
    Function.Injective (formAssociatedIdealIntegerLinearMap D Q hQ) := by
  intro v w hvw
  have hpair : (v 0, v 1) = (w 0, w 1) :=
    formAssociatedIdeal_int_coordinates_injective D Q hQ ha
      (congrArg Subtype.val hvw)
  funext i
  fin_cases i
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

/-- At positive fundamental discriminant, the coordinate map is an integer
linear equivalence onto the actual attached ideal. -/
noncomputable def formAssociatedIdealIntegerLinearEquivAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (Fin 2 → ℤ) ≃ₗ[ℤ] formAssociatedIdeal (D : ℤ) Q.1 Q.2.2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  apply LinearEquiv.ofBijective (formAssociatedIdealIntegerLinearMap (D : ℤ) Q.1 Q.2.2)
  constructor
  · exact formAssociatedIdealIntegerLinearMap_injective (D : ℤ) Q.1 Q.2.2
      (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q)
  · intro z
    obtain ⟨p, hp, _⟩ := formAssociatedIdeal_existsUnique_int_coordinates D hD Q z
    refine ⟨![p.1, p.2], ?_⟩
    apply Subtype.ext
    exact hp.symm

/-- The forward equivalence preserves the literal `a*x - theta*y` formula. -/
@[simp]
theorem coe_formAssociatedIdealIntegerLinearEquivAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) (v : Fin 2 → ℤ) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (formAssociatedIdealIntegerLinearEquivAtPositiveFundamentalDiscriminant D hD Q v :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        formIdealVector (D : ℤ) Q.1 Q.2.2 (v 0) (v 1) := by
  rfl

/-- The actual attached ideal has the integer basis indexed by `Fin 2`
whose vectors are `a` and `-theta`, in that order. -/
noncomputable def formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    Module.Basis (Fin 2) ℤ (formAssociatedIdeal (D : ℤ) Q.1 Q.2.2) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact Module.Basis.ofEquivFun
    (formAssociatedIdealIntegerLinearEquivAtPositiveFundamentalDiscriminant D hD Q).symm

/-- The first basis vector is the leading coefficient. -/
@[simp]
theorem formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant_zero
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant D hD Q 0 :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) = Q.1.a := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  rw [formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant,
    Module.Basis.coe_ofEquivFun]
  change formIdealVector (D : ℤ) Q.1 Q.2.2
    ((Pi.single 0 1 : Fin 2 → ℤ) 0) ((Pi.single 0 1 : Fin 2 → ℤ) 1) = _
  simp [formIdealVector]

/-- The second basis vector is the negative quadratic generator. -/
@[simp]
theorem formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant D hD Q 1 :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
        -formIdealGenerator (D : ℤ) Q.1 Q.2.2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  rw [formAssociatedIdealIntegerBasisAtPositiveFundamentalDiscriminant,
    Module.Basis.coe_ofEquivFun]
  change formIdealVector (D : ℤ) Q.1 Q.2.2
    ((Pi.single 1 1 : Fin 2 → ℤ) 0) ((Pi.single 1 1 : Fin 2 → ℤ) 1) = _
  simp [formIdealVector]

end
end IntegralBinaryQuadraticForm
end PellPaper
