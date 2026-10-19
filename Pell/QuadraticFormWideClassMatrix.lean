import Pell.QuadraticFormWideClassScalingEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# A unimodular coordinate matrix from equal attached wide ideal classes

The proved ideal-coordinate equivalences turn the actual lattice
equivalence supplied by wide-class equality into an integer matrix with
unit determinant.  Its coordinate action satisfies the literal vector
scaling relation.  No basis, lattice equality, or matrix invertibility is
assumed as an extra input.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_wideClassMatrix_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Equal attached wide ideal classes yield a unimodular integer matrix
intertwining the actual ideal vectors through two nonzero integral factors. -/
theorem exists_unimodular_formIdealVector_scale_of_wideClass_eq
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q R : PrimitiveBinaryQuadraticForms (D : ℤ))
    (hclass : formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q =
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD R) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∃ x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      x ≠ 0 ∧ y ≠ 0 ∧
      ∃ M : Matrix (Fin 2) (Fin 2) ℤ, IsUnit M.det ∧
        ∀ v : Fin 2 → ℤ,
          y * formIdealVector (D : ℤ) R.1 R.2.2 (M.mulVec v 0) (M.mulVec v 1) =
            x * formIdealVector (D : ℤ) Q.1 Q.2.2 (v 0) (v 1) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  obtain ⟨x, y, hx, hy, e, he⟩ :=
    exists_formAssociatedIdeal_integerLinearEquiv_of_wideClass_eq D hD Q R hclass
  let bQ := formAssociatedIdealIntegerLinearEquivAtPositiveFundamentalDiscriminant D hD Q
  let bR := formAssociatedIdealIntegerLinearEquivAtPositiveFundamentalDiscriminant D hD R
  let E : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) := (bQ.trans e).trans bR.symm
  refine ⟨x, y, hx, hy, LinearMap.toMatrix' E.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact E.isUnit_det'
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    change y * (bR (E v) : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
      x * (bQ v : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
    have hE : bR (E v) = e (bQ v) := bR.apply_symm_apply _
    rw [hE]
    exact he (bQ v)

end
end IntegralBinaryQuadraticForm
end PellPaper
