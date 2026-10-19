import Pell.QuadraticFormRawLatticeFibre

/-! Equal raw lattices in a common ideal give at most two proper-form classes. -/

namespace PellPaper.IntegralBinaryQuadraticForm

noncomputable section

local instance commonRawLattice_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) := rationalQuadraticAlgebra_numberField D

theorem properEquivalent_or_wideClassPartner_of_common_rawLattice_scale
    (D : ℤ) (Q R : PrimitiveBinaryQuadraticForms D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (J : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (eQ : formAssociatedIdeal D Q.1 Q.2.2 ≃ₗ[ℤ] J)
    (eR : formAssociatedIdeal D R.1 R.2.2 ≃ₗ[ℤ] J)
    (xQ yQ xR yR : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    (hyQ : yQ ≠ 0) (hxR : xR ≠ 0)
    (hQ : ∀ z : formAssociatedIdeal D Q.1 Q.2.2,
      yQ * (eQ z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = xQ * z.1)
    (hR : ∀ z : formAssociatedIdeal D R.1 R.2.2,
      yR * (eR z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = xR * z.1)
    (hcommon : (formAssociatedIdealIntegerLinearMap D Q.1 Q.2.2).range.map eQ.toLinearMap =
      (formAssociatedIdealIntegerLinearMap D R.1 R.2.2).range.map eR.toLinearMap) :
    ProperEquivalent R Q ∨ ProperEquivalent R (wideClassPartnerAt Q) := by
  let E := eQ.trans eR.symm
  have hE (z : formAssociatedIdeal D Q.1 Q.2.2) : eR (E z) = eQ z :=
    eR.apply_symm_apply _
  apply properEquivalent_or_wideClassPartner_of_rawLattice_scale D Q R E
    (yR * xQ) (xR * yQ) (mul_ne_zero hxR hyQ)
  · intro z
    calc
      (xR * yQ) * (E z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
          yQ * (xR * (E z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) := by ring
      _ = yQ * (yR * (eR (E z) : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) := by
        rw [hR]
      _ = yQ * (yR * (eQ z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) := by rw [hE]
      _ = yR * (yQ * (eQ z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) := by ring
      _ = yR * (xQ * z.1) := by rw [hQ]
      _ = (yR * xQ) * z.1 := by ring
  · have h := congrArg (fun N : Submodule ℤ J => N.map eR.symm.toLinearMap) hcommon
    rw [← Submodule.map_comp, ← Submodule.map_comp] at h
    have hid : eR.symm.toLinearMap.comp eR.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro z
      exact eR.symm_apply_apply z
    rw [hid, Submodule.map_id] at h
    exact h

end
end PellPaper.IntegralBinaryQuadraticForm
