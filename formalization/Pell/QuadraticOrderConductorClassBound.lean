import Pell.QuadraticOrderWideClassFibreBound
import Pell.QuadraticOrderWideClassNumber

/-! A uniform divisor-sum conductor bound for the actual proper-form quotient. -/

namespace PellPaper.IntegralBinaryQuadraticForm

open scoped BigOperators

noncomputable section

local instance conductorClassBound_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) := rationalQuadraticAlgebra_numberField D

/-- The actual proper class number at conductor `f` is bounded uniformly by
twice `sigma₁(f)` times the fundamental proper class number. -/
theorem properFormClass_card_mul_sq_le_two_mul_divisorSum
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    Nat.card (ProperFormClass (((D₀ * f ^ 2 : ℕ) : ℤ))) ≤
      2 * (∑ a ∈ f.divisors, a) * Nat.card (ProperFormClass (D₀ : ℤ)) := by
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
  let D : ℤ := ((D₀ * f ^ 2 : ℕ) : ℤ)
  let classMap := properFormClassWideClassMap D
  have hfibre (c : ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) :
      Finite {C : ProperFormClass D // classMap C = c} ∧
      Nat.card {C : ProperFormClass D // classMap C = c} ≤ 2 * ∑ a ∈ f.divisors, a :=
    properFormClassWideClassMap_fibre_finite_and_card_le_two_mul_divisorSum D₀ f hD₀ hf c
  let _ : ∀ c, Finite {C : ProperFormClass D // classMap C = c} := fun c => (hfibre c).1
  calc
    Nat.card (ProperFormClass D) =
        Nat.card (Σ c, {C : ProperFormClass D // classMap C = c}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv classMap)).symm
    _ = ∑ c, Nat.card {C : ProperFormClass D // classMap C = c} := Nat.card_sigma
    _ ≤ ∑ _c : ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)),
        2 * ∑ a ∈ f.divisors, a :=
      Finset.sum_le_sum fun c _ => (hfibre c).2
    _ = (2 * ∑ a ∈ f.divisors, a) *
        Nat.card (ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) := by
      simp [Nat.card_eq_fintype_card, mul_comm]
    _ ≤ (2 * ∑ a ∈ f.divisors, a) * Nat.card (ProperFormClass (D₀ : ℤ)) :=
      Nat.mul_le_mul_left _
        (natCard_classGroup_rationalQuadraticAlgebra_nat_mul_sq_le_properFormClass_card D₀ f hD₀ hf)

/-- The literal real-valued conductor comparison required by the average pipeline. -/
theorem properFormClass_card_mul_sq_le_two_mul_divisorSum_real
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    (Nat.card (ProperFormClass (((D₀ * f ^ 2 : ℕ) : ℤ))) : ℝ) ≤
      2 * (∑ a ∈ f.divisors, (a : ℝ)) * (Nat.card (ProperFormClass (D₀ : ℤ)) : ℝ) := by
  have h := (Nat.cast_le (α := ℝ)).mpr
    (properFormClass_card_mul_sq_le_two_mul_divisorSum D₀ f hD₀ hf)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using h

end
end PellPaper.IntegralBinaryQuadraticForm
