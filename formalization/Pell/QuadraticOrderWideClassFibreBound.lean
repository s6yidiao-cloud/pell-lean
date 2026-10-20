import Pell.QuadraticOrderProperClassWideClassMap
import Pell.QuadraticFormCommonRawLatticeFibre
import Pell.RankTwoSublatticeTransport
import Mathlib.Logic.Equiv.Sum

/-!
# Wide-class fibres for nonmaximal quadratic discriminants

For a primitive form of discriminant `D₀ f²`, its two literal form vectors
span an index-`f` sublattice of its attached maximal-order ideal.  Inside one
fibre of the actual map to the wide ideal class group, principal scaling
transports every such raw lattice to a fixed attached ideal.  There are at
most `sigma₁(f)` possible transported lattices, and equality of two of them
leaves at most the usual form/partner ambiguity.

This proves a fibre bound only.  It asserts neither surjectivity nor a narrow
class correspondence.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

open scoped BigOperators

local instance quadraticOrderWideClassFibreBound_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private structure PrincipalScaleData (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (Q R : PrimitiveBinaryQuadraticForms D) where
  x : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)
  y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  equiv : formAssociatedIdeal D Q.1 Q.2.2 ≃ₗ[ℤ]
    formAssociatedIdeal D R.1 R.2.2
  scale : ∀ z : formAssociatedIdeal D Q.1 Q.2.2,
    y * (equiv z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
      x * z.1

private theorem nonempty_principalScaleData_of_wideClass_eq
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (Q R : PrimitiveBinaryQuadraticForms D)
    (hclass : primitiveFormAssociatedIdealClass D Q =
      primitiveFormAssociatedIdealClass D R) :
    Nonempty (PrincipalScaleData D Q R) := by
  have haQ : Q.1.a ≠ 0 :=
    leadingCoefficient_ne_zero_of_noRationalRoot D Q.1 Q.2.2
  have haR : R.1.a ≠ 0 :=
    leadingCoefficient_ne_zero_of_noRationalRoot D R.1 R.2.2
  have hIQ : formAssociatedIdeal D Q.1 Q.2.2 ≠ ⊥ :=
    formAssociatedIdeal_ne_bot_of_a_ne_zero D Q.1 Q.2.2 haQ
  have hIR : formAssociatedIdeal D R.1 R.2.2 ≠ ⊥ :=
    formAssociatedIdeal_ne_bot_of_a_ne_zero D R.1 R.2.2 haR
  have hclass' :
      idealClassOfNonzeroIdeal (formAssociatedIdeal D Q.1 Q.2.2) hIQ =
        idealClassOfNonzeroIdeal (formAssociatedIdeal D R.1 R.2.2) hIR := by
    simpa [primitiveFormAssociatedIdealClass, formAssociatedIdealClass] using hclass
  obtain ⟨x, y, hx, hy, e, he⟩ :=
    exists_principalScaleLinearEquiv_of_idealClass_eq
      (formAssociatedIdeal D Q.1 Q.2.2)
      (formAssociatedIdeal D R.1 R.2.2) hIQ hIR hclass'
  exact ⟨⟨x, y, hx, hy, e.restrictScalars ℤ, he⟩⟩

private theorem finite_and_card_le_two_of_injective_cover
    {α β : Type*} (i : α → β) (hi : Function.Injective i)
    (a b : β) (hcover : ∀ z : α, i z = a ∨ i z = b) :
    Finite α ∧ Nat.card α ≤ 2 := by
  classical
  let g : α → ({a, b} : Finset β) := fun z =>
    ⟨i z, by simpa using hcover z⟩
  have hg : Function.Injective g := by
    intro z w hzw
    apply hi
    exact congrArg (fun u : ({a, b} : Finset β) => u.1) hzw
  refine ⟨Finite.of_injective g hg, ?_⟩
  calc
    Nat.card α ≤ Nat.card ({a, b} : Finset β) :=
      Nat.card_le_card_of_injective g hg
    _ = ({a, b} : Finset β).card := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

/-- Every fibre of the actual wide-class map at discriminant `D₀ f²` is
finite and has cardinality at most twice the divisor sum of `f`. -/
theorem properFormClassWideClassMap_fibre_finite_and_card_le_two_mul_divisorSum
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    let _ : Fact
        (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
    ∀ c : ClassGroup (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ)))),
      Finite {C : ProperFormClass (((D₀ * f ^ 2 : ℕ) : ℤ)) //
        properFormClassWideClassMap (((D₀ * f ^ 2 : ℕ) : ℤ)) C = c} ∧
      Nat.card {C : ProperFormClass (((D₀ * f ^ 2 : ℕ) : ℤ)) //
        properFormClassWideClassMap (((D₀ * f ^ 2 : ℕ) : ℤ)) C = c} ≤
        2 * ∑ a ∈ f.divisors, a := by
  classical
  let _ : Fact
      (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
  dsimp only
  intro c
  let D : ℤ := ((D₀ * f ^ 2 : ℕ) : ℤ)
  let classMap := properFormClassWideClassMap D
  let A := {C : ProperFormClass D // classMap C = c}
  change Finite A ∧ Nat.card A ≤ 2 * ∑ a ∈ f.divisors, a
  by_cases hA : Nonempty A
  · obtain ⟨C₀⟩ := hA
    let Q₀ : PrimitiveBinaryQuadraticForms D := Quotient.out C₀.1
    let J : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
      formAssociatedIdeal D Q₀.1 Q₀.2.2
    have haQ₀ : Q₀.1.a ≠ 0 :=
      leadingCoefficient_ne_zero_of_noRationalRoot D Q₀.1 Q₀.2.2
    have hJ : J ≠ ⊥ :=
      formAssociatedIdeal_ne_bot_of_a_ne_zero D Q₀.1 Q₀.2.2 haQ₀
    let bJ : Module.Basis (Fin 2) ℤ J := quadraticIdealIntegerBasis D J hJ
    let rep (C : A) : PrimitiveBinaryQuadraticForms D := Quotient.out C.1
    have hrepClass (C : A) :
        primitiveFormAssociatedIdealClass D (rep C) =
          primitiveFormAssociatedIdealClass D Q₀ := by
      calc
        primitiveFormAssociatedIdealClass D (rep C) =
            classMap (PrimitiveBinaryQuadraticForms.toProperFormClass (rep C)) :=
          (properFormClassWideClassMap_apply_toProperFormClass D (rep C)).symm
        _ = classMap C.1 := congrArg classMap (Quotient.out_eq C.1)
        _ = c := C.2
        _ = classMap C₀.1 := C₀.2.symm
        _ = classMap (PrimitiveBinaryQuadraticForms.toProperFormClass Q₀) :=
          congrArg classMap (Quotient.out_eq C₀.1).symm
        _ = primitiveFormAssociatedIdealClass D Q₀ :=
          properFormClassWideClassMap_apply_toProperFormClass D Q₀
    let scaleData (C : A) : PrincipalScaleData D (rep C) Q₀ :=
      Classical.choice
        (nonempty_principalScaleData_of_wideClass_eq D (rep C) Q₀ (hrepClass C))
    let transportedRange (C : A) : Submodule ℤ J :=
      (formAssociatedIdealIntegerLinearMap D (rep C).1 (rep C).2.2).range.map
        (scaleData C).equiv.toLinearMap
    have htransportedRangeIndex (C : A) :
        (transportedRange C).toAddSubgroup.index = f := by
      calc
        (transportedRange C).toAddSubgroup.index =
            (formAssociatedIdealIntegerLinearMap D
              (rep C).1 (rep C).2.2).range.toAddSubgroup.index := by
          dsimp only [transportedRange]
          rw [Submodule.map_toAddSubgroup]
          exact (formAssociatedIdealIntegerLinearMap D
            (rep C).1 (rep C).2.2).range.toAddSubgroup.index_map_equiv
              (scaleData C).equiv.toAddEquiv
        _ = f := by
          simpa [D] using
            (formAssociatedIdealIntegerLinearMap_range_index_eq_conductor
              D₀ f hD₀ hf (rep C))
    let B := {N : Submodule ℤ J // N.toAddSubgroup.index = f}
    let rawRange (C : A) : B :=
      ⟨transportedRange C, htransportedRangeIndex C⟩
    have hBfinite : Finite B := by
      dsimp only [B]
      exact finite_rankTwoSublatticesOfIndex_of_basis bJ f hf
    have hBcard : Nat.card B ≤ ∑ a ∈ f.divisors, a := by
      dsimp only [B]
      exact card_rankTwoSublatticesOfIndex_le_of_basis bJ f hf
    have hrawFibre (N : B) :
        Finite {C : A // rawRange C = N} ∧
          Nat.card {C : A // rawRange C = N} ≤ 2 := by
      by_cases hN : Nonempty {C : A // rawRange C = N}
      · obtain ⟨Cbase⟩ := hN
        apply finite_and_card_le_two_of_injective_cover
          (fun C : {C : A // rawRange C = N} => C.1.1)
          (by
            intro C R hCR
            apply Subtype.ext
            apply Subtype.ext
            exact hCR)
          Cbase.1.1
          (PrimitiveBinaryQuadraticForms.toProperFormClass
            (wideClassPartnerAt (rep Cbase.1)))
        intro C
        have hcommon : transportedRange Cbase.1 = transportedRange C.1 := by
          exact congrArg Subtype.val (Cbase.2.trans C.2.symm)
        rcases properEquivalent_or_wideClassPartner_of_common_rawLattice_scale
            D (rep Cbase.1) (rep C.1) J
            (scaleData Cbase.1).equiv (scaleData C.1).equiv
            (scaleData Cbase.1).x (scaleData Cbase.1).y
            (scaleData C.1).x (scaleData C.1).y
            (scaleData Cbase.1).y_ne_zero (scaleData C.1).x_ne_zero
            (scaleData Cbase.1).scale (scaleData C.1).scale hcommon with h | h
        · left
          calc
            C.1.1 = PrimitiveBinaryQuadraticForms.toProperFormClass (rep C.1) :=
              (Quotient.out_eq C.1.1).symm
            _ = PrimitiveBinaryQuadraticForms.toProperFormClass (rep Cbase.1) :=
              Quotient.sound h
            _ = Cbase.1.1 := Quotient.out_eq Cbase.1.1
        · right
          calc
            C.1.1 = PrimitiveBinaryQuadraticForms.toProperFormClass (rep C.1) :=
              (Quotient.out_eq C.1.1).symm
            _ = PrimitiveBinaryQuadraticForms.toProperFormClass
                (wideClassPartnerAt (rep Cbase.1)) := Quotient.sound h
      · let _ : IsEmpty {C : A // rawRange C = N} :=
          ⟨fun C => hN ⟨C⟩⟩
        exact ⟨inferInstance, by simp⟩
    let _ : Finite B := hBfinite
    let _ : Fintype B := Fintype.ofFinite B
    let _ : ∀ N : B, Finite {C : A // rawRange C = N} :=
      fun N => (hrawFibre N).1
    have hAfinite : Finite A :=
      Finite.of_equiv (Σ N, {C : A // rawRange C = N})
        (Equiv.sigmaFiberEquiv rawRange)
    refine ⟨hAfinite, ?_⟩
    let _ : Finite A := hAfinite
    calc
      Nat.card A = Nat.card (Σ N, {C : A // rawRange C = N}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv rawRange)).symm
      _ = ∑ N : B, Nat.card {C : A // rawRange C = N} := Nat.card_sigma
      _ ≤ ∑ _N : B, 2 := by
        apply Finset.sum_le_sum
        intro N _
        exact (hrawFibre N).2
      _ = 2 * Nat.card B := by
        simp [mul_comm]
      _ ≤ 2 * ∑ a ∈ f.divisors, a := Nat.mul_le_mul_left 2 hBcard
  · let _ : IsEmpty A := ⟨fun C => hA ⟨C⟩⟩
    exact ⟨inferInstance, by simp⟩

end
end IntegralBinaryQuadraticForm
end PellPaper
