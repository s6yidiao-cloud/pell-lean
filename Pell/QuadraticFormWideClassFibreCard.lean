import Pell.QuadraticFormWideClassFibre
import Pell.QuadraticFormProperClassWideClassMap
import Pell.QuadraticAlgebraClassNumber
import Mathlib.Logic.Equiv.Sum

/-!
# Finite fibres and a genuine bound for the proper-form class count

The actual wide-class-map fibre through a primitive representative is
covered by its proper class and the proper class of its partner.  Every
fibre is therefore finite of cardinality at most two, including empty
fibres.  The actual finite ideal class group then gives finiteness of the
proper-form quotient and the bound `card <= 2 * classNumber`.

Finiteness is established before the natural-cardinality bound.  No
surjectivity or equality of class numbers is asserted.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_wideClassFibreCard_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem finite_and_card_le_two_of_subset_pair {α : Type*}
    (s : Set α) (a b : α) (hcover : ∀ z ∈ s, z = a ∨ z = b) :
    Finite s ∧ Nat.card s ≤ 2 := by
  classical
  let g : s → ({a, b} : Finset α) :=
    fun z => ⟨z.1, by simpa using hcover z.1 z.2⟩
  have hg : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    exact congrArg (fun z : ({a, b} : Finset α) => z.1) h
  refine ⟨Finite.of_injective g hg, ?_⟩
  calc
    Nat.card s ≤ Nat.card ({a, b} : Finset α) := Nat.card_le_card_of_injective g hg
    _ = ({a, b} : Finset α).card := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

/-- Explicit two-point coverage of the actual quotient-map fibre through a
primitive representative, before any cardinality is taken. -/
theorem properFormClassWideClassMap_fibre_covered_by_partner
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) (C : ProperFormClass (D : ℤ))
    (hC : properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD C =
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q) :
    C = PrimitiveBinaryQuadraticForms.toProperFormClass Q ∨
      C = PrimitiveBinaryQuadraticForms.toProperFormClass (wideClassPartnerAt Q) := by
  revert hC
  refine Quotient.inductionOn C ?_
  intro R hR
  change formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD R =
    formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q at hR
  rcases properEquivalent_or_wideClassPartner_of_attachedWideClass_eq D hD Q R hR.symm
    with h | h
  · exact Or.inl (Quotient.sound h)
  · exact Or.inr (Quotient.sound h)

/-- Every fibre of the actual map to the wide ideal class group is finite
and has cardinality at most two; no nonemptiness or surjectivity is required. -/
theorem properFormClassWideClassMap_fibre_finite_and_card_le_two
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ c : ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      Finite {C : ProperFormClass (D : ℤ) //
        properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD C = c} ∧
      Nat.card {C : ProperFormClass (D : ℤ) //
        properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD C = c} ≤ 2 := by
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro c
  let f := properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD
  by_cases hc : ∃ C, f C = c
  · obtain ⟨C, hC⟩ := hc
    revert hC
    refine Quotient.inductionOn C ?_
    intro Q hQ
    apply finite_and_card_le_two_of_subset_pair
      {C : ProperFormClass (D : ℤ) | f C = c}
      (PrimitiveBinaryQuadraticForms.toProperFormClass Q)
      (PrimitiveBinaryQuadraticForms.toProperFormClass (wideClassPartnerAt Q))
    intro Z hZ
    apply properFormClassWideClassMap_fibre_covered_by_partner D hD Q Z
    exact hZ.trans hQ.symm
  · let : IsEmpty {C : ProperFormClass (D : ℤ) // f C = c} :=
      ⟨fun C => hc ⟨C.1, C.2⟩⟩
    exact ⟨inferInstance, by simp⟩

/-- The literal proper-form quotient at a positive fundamental discriminant
is finite, using the proved finite fibres over the actual finite class group. -/
theorem finite_properFormClass_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    Finite (ProperFormClass (D : ℤ)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let f := properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD
  let : ∀ c, Finite {C : ProperFormClass (D : ℤ) // f C = c} :=
    fun c => (properFormClassWideClassMap_fibre_finite_and_card_le_two D hD c).1
  exact Finite.of_equiv (Σ c, {C : ProperFormClass (D : ℤ) // f C = c})
    (Equiv.sigmaFiberEquiv f)

/-- The genuine finite proper-form class count is bounded by twice the
actual wide ideal class number.  This is a bound, not a class correspondence
or a surjectivity statement. -/
theorem properFormClass_card_le_two_mul_classNumber
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    Nat.card (ProperFormClass (D : ℤ)) ≤
      2 * rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let := finite_properFormClass_of_positiveFundamentalDiscriminant D hD
  let f := properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD
  let : ∀ c, Finite {C : ProperFormClass (D : ℤ) // f C = c} :=
    fun c => (properFormClassWideClassMap_fibre_finite_and_card_le_two D hD c).1
  calc
    Nat.card (ProperFormClass (D : ℤ)) =
        Nat.card (Σ c, {C : ProperFormClass (D : ℤ) // f C = c}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ c, Nat.card {C : ProperFormClass (D : ℤ) // f C = c} := Nat.card_sigma
    _ ≤ ∑ _c : ClassGroup
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))), 2 := by
      apply Finset.sum_le_sum
      intro c _
      exact (properFormClassWideClassMap_fibre_finite_and_card_le_two D hD c).2
    _ = 2 * rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
      simp [rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant,
        rationalQuadraticAlgebraClassNumber, NumberField.classNumber, mul_comm]

end
end IntegralBinaryQuadraticForm
end PellPaper
