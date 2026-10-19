import Pell.QuadraticFormWideClassFibre

/-!
# Proper-form ambiguity after matching raw lattices

An ideal equivalence compatible with scalar multiplication need not preserve
the raw rank-two lattices. When it does, their integer coordinate equivalences
give a unimodular substitution and at most the usual two proper classes.
No fundamental-discriminant or full-ideal coordinate-surjectivity assumption
is made here.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rawLatticeFibre_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) := rationalQuadraticAlgebra_numberField D

theorem properEquivalent_or_wideClassPartner_of_rawLattice_scale
    (D : ℤ) (Q R : PrimitiveBinaryQuadraticForms D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (e : formAssociatedIdeal D Q.1 Q.2.2 ≃ₗ[ℤ] formAssociatedIdeal D R.1 R.2.2)
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) (hy : y ≠ 0)
    (hscale : ∀ z : formAssociatedIdeal D Q.1 Q.2.2,
      y * (e z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = x * z.1)
    (hrange : (formAssociatedIdealIntegerLinearMap D Q.1 Q.2.2).range.map e.toLinearMap =
      (formAssociatedIdealIntegerLinearMap D R.1 R.2.2).range) :
    ProperEquivalent R Q ∨ ProperEquivalent R (wideClassPartnerAt Q) := by
  have ha : ∀ S : PrimitiveBinaryQuadraticForms D, S.1.a ≠ 0 := by
    intro S hSa
    apply Fact.out (p := rationalQuadraticAlgebraNoRationalRoot D) (S.1.b : ℚ)
    exact_mod_cast (by simpa [discriminant, hSa] using S.2.2)
  let gQ := formAssociatedIdealIntegerLinearMap D Q.1 Q.2.2
  let gR := formAssociatedIdealIntegerLinearMap D R.1 R.2.2
  let bQ := LinearEquiv.ofInjective gQ
    (formAssociatedIdealIntegerLinearMap_injective D Q.1 Q.2.2 (ha Q))
  let bR := LinearEquiv.ofInjective gR
    (formAssociatedIdealIntegerLinearMap_injective D R.1 R.2.2 (ha R))
  let er := e.ofSubmodules gQ.range gR.range hrange
  let E : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) := (bQ.trans er).trans bR.symm
  let M := LinearMap.toMatrix' E.toLinearMap
  have hM : IsUnit M.det := by
    rw [LinearMap.det_toMatrix']
    exact E.isUnit_det'
  have hvec : ∀ v : Fin 2 → ℤ,
      y * formIdealVector D R.1 R.2.2 (M.mulVec v 0) (M.mulVec v 1) =
        x * formIdealVector D Q.1 Q.2.2 (v 0) (v 1) := by
    intro v
    rw [LinearMap.toMatrix'_mulVec]
    have hE : bR (E v) = er (bQ v) := bR.apply_symm_apply _
    have hcoord : gR (E v) = e (gQ v) := congrArg Subtype.val hE
    change y * (gR (E v) : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
      x * (gQ v : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    rw [hcoord]
    exact hscale (gQ v)
  apply properEquivalent_or_partner_of_unimodular_eval Q R M hM
  exact eval_transform_eq_det_mul_of_vector_scale D Q.1 R.1 Q.2.2 R.2.2
    x y hy (ha R) M hvec

end
end IntegralBinaryQuadraticForm
end PellPaper
