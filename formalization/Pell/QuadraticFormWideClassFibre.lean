import Pell.QuadraticFormWideClassMatrix
import Pell.QuadraticFormIdealScaleDeterminant
import Pell.QuadraticFormWideClassPartner

/-!
# The two possible proper-form classes over an attached wide ideal class

Two primitive forms of positive fundamental discriminant with equal attached
wide ideal classes are properly equivalent either to one another or to the
partner `[-a,b,-c]`.  Actual ideal-class equality supplies the lattice
equivalence and unimodular matrix; the determinant and vector norm identities
then give the two proper-substitution alternatives.

The two alternatives need not be distinct.  No surjectivity of the map to
the wide ideal class group or class-number equality is claimed here.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

open scoped MatrixGroups

private theorem eq_of_eval_eq (Q R : IntegralBinaryQuadraticForm)
    (h : ∀ x y : ℤ, Q.eval x y = R.eval x y) : Q = R := by
  have ha := h 1 0
  have hc := h 0 1
  have habc := h 1 1
  norm_num [eval] at ha hc habc
  exact ext ha (by omega) hc

/-- A unimodular signed form identity yields proper equivalence to the form
or its partner.  In the negative-determinant case, negating the second matrix
column restores determinant one and gives precisely `[-a,b,-c]`. -/
theorem properEquivalent_or_partner_of_unimodular_eval
    {D : ℤ} (Q R : PrimitiveBinaryQuadraticForms D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : IsUnit M.det)
    (hform : ∀ v : Fin 2 → ℤ,
      R.1.eval (M.mulVec v 0) (M.mulVec v 1) = M.det * Q.1.eval (v 0) (v 1)) :
    ProperEquivalent R Q ∨ ProperEquivalent R (wideClassPartnerAt Q) := by
  rcases Int.isUnit_iff.mp hM with hM | hM
  · let g : SL(2, ℤ) := ⟨M, hM⟩
    left
    refine ⟨g, ?_⟩
    apply Subtype.ext
    change R.1.properTransform g = Q.1
    apply eq_of_eval_eq
    intro x y
    rw [eval_properTransform]
    simpa [g, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hM] using hform ![x, y]
  · let N : Matrix (Fin 2) (Fin 2) ℤ := !![M 0 0, -M 0 1; M 1 0, -M 1 1]
    have hN : N.det = 1 := by
      have hM' := hM
      rw [Matrix.det_fin_two] at hM'
      dsimp [N]
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -hM'
    let g : SL(2, ℤ) := ⟨N, hN⟩
    right
    refine ⟨g, ?_⟩
    apply Subtype.ext
    change R.1.properTransform g = Q.1.wideClassPartner
    apply eq_of_eval_eq
    intro x y
    rw [eval_properTransform, eval_wideClassPartner]
    simpa [g, N, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hM] using hform ![x, -y]

local instance rationalQuadraticAlgebra_wideClassFibre_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Equality of the actual attached wide ideal classes puts two primitive
forms into the same proper class or the partner proper class.  All lattice
and determinant statements used in this conclusion are proved internally. -/
theorem properEquivalent_or_wideClassPartner_of_attachedWideClass_eq
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q R : PrimitiveBinaryQuadraticForms (D : ℤ))
    (hclass : formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q =
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD R) :
    ProperEquivalent R Q ∨ ProperEquivalent R (wideClassPartnerAt Q) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  obtain ⟨x, y, _hx, hy, M, hM, hscale⟩ :=
    exists_unimodular_formIdealVector_scale_of_wideClass_eq D hD Q R hclass
  apply properEquivalent_or_partner_of_unimodular_eval Q R M hM
  exact eval_transform_eq_det_mul_of_vector_scale (D : ℤ) Q.1 R.1 Q.2.2 R.2.2
    x y hy (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD R) M hscale

end
end IntegralBinaryQuadraticForm
end PellPaper
