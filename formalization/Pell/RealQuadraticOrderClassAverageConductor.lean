import Pell.RealQuadraticOrderClassAverage
import Pell.QuadraticOrderFormClassFiniteness
import Pell.QuadraticOrderConductorCover
import Pell.ConductorDivisorSeries
import Pell.ClassAverageScaleRatio
import Pell.RealQuadraticFieldClassAverageUniformExceptional

/-!
# Transfer of the fundamental average through conductors

The analytic transfer to all positive nonsquare order discriminants needs
no order L-function or separate large-conductor estimate. A uniform ratio
bound for the exact logarithmic scale and the convergent divisor-weighted
conductor series suffice. The actual pointwise conductor class-number
comparison remains an explicit, unproved arithmetic premise.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A divisor-sum conductor bound for actual proper-form class numbers
transfers the literal fundamental-discriminant average to the complete
order-discriminant average. All-order finiteness is supplied internally. -/
theorem realQuadraticOrderClassAverageAssertion_of_conductorBound
    (A : ℝ) (hA : 0 < A)
    (hconductor : ∀ D₀ f : ℕ, PositiveFundamentalDiscriminant D₀ → 0 < f →
      (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass ((D₀ * f ^ 2 : ℕ) : ℤ)) : ℝ) ≤
        A * (∑ d ∈ f.divisors, (d : ℝ)) *
          (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D₀ : ℤ)) : ℝ))
    (hfundamental : RealQuadraticFieldClassAverageAssertion) :
    RealQuadraticOrderClassAverageAssertion := by
  classical
  obtain ⟨C, hC, hfund⟩ := hfundamental
  obtain ⟨K, hK, hratio⟩ := exists_pos_classAverageScale_le_ratio_rpow
  obtain ⟨B, hB, hbudget⟩ := exists_pos_sum_divisors_div_rpow_five_halves_le
  refine ⟨fun D hD ↦
    IntegralBinaryQuadraticForm.finite_properFormClass_of_positiveQuadraticOrderDiscriminant hD,
    A * C * K * B, by positivity, ?_⟩
  intro X hX
  refine ⟨realQuadraticFieldClassSum_le_orderFormClassSum X, ?_⟩
  let w : ℕ → ℝ := fun D ↦
    (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ)
  have hw (D : ℕ) : 0 ≤ w D := Nat.cast_nonneg _
  have hXpos : 0 < X := by linarith
  have hscale : 0 ≤ classAverageScale X := classAverageScale_nonneg (by linarith)
  have hinner (f : ℕ) (hf : f ∈ Finset.Icc 1 ⌈X⌉₊) :
      (∑ D₀ ∈ fundamentalDiscriminantsBelow (X / (f : ℝ) ^ 2), w (D₀ * f ^ 2)) ≤
        (A * C * K * classAverageScale X) *
          ((∑ d ∈ f.divisors, (d : ℝ)) / (f : ℝ) ^ (5 / 2 : ℝ)) := by
    have hfpos : 0 < f := (Finset.mem_Icc.mp hf).1
    have hfreal : 0 < (f : ℝ) := by exact_mod_cast hfpos
    have hfone : 1 ≤ (f : ℝ) := by exact_mod_cast hfpos
    let Y : ℝ := X / (f : ℝ) ^ 2
    have hYpos : 0 < Y := div_pos hXpos (sq_pos_of_pos hfreal)
    have hYX : Y ≤ X := div_le_self hXpos.le (by nlinarith)
    have hsigma : 0 ≤ ∑ d ∈ f.divisors, (d : ℝ) :=
      Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    by_cases hY : 3 ≤ Y
    · have hcon : (∑ D₀ ∈ fundamentalDiscriminantsBelow Y, w (D₀ * f ^ 2)) ≤
          A * (∑ d ∈ f.divisors, (d : ℝ)) *
            (∑ D₀ ∈ fundamentalDiscriminantsBelow Y, w D₀) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro D₀ hD₀
        exact hconductor D₀ f (mem_fundamentalDiscriminantsBelow.mp hD₀).1 hfpos
      have hp : (Y / X) ^ (5 / 4 : ℝ) = 1 / (f : ℝ) ^ (5 / 2 : ℝ) := by
        have heq : Y / X = 1 / (f : ℝ) ^ 2 := by dsimp [Y]; field_simp
        rw [heq, Real.div_rpow (by norm_num) (sq_nonneg _), Real.one_rpow,
          ← Real.rpow_natCast_mul hfreal.le]
        norm_num
      calc
        (∑ D₀ ∈ fundamentalDiscriminantsBelow (X / (f : ℝ) ^ 2), w (D₀ * f ^ 2)) ≤
            A * (∑ d ∈ f.divisors, (d : ℝ)) *
              (∑ D₀ ∈ fundamentalDiscriminantsBelow Y, w D₀) := hcon
        _ ≤ A * (∑ d ∈ f.divisors, (d : ℝ)) * (C * classAverageScale Y) :=
          mul_le_mul_of_nonneg_left (hfund Y hY).2 (mul_nonneg hA.le hsigma)
        _ ≤ A * (∑ d ∈ f.divisors, (d : ℝ)) *
            (C * (K * (Y / X) ^ (5 / 4 : ℝ) * classAverageScale X)) := by
          gcongr
          exact hratio Y X hY hYX
        _ = (A * C * K * classAverageScale X) *
            ((∑ d ∈ f.divisors, (d : ℝ)) / (f : ℝ) ^ (5 / 2 : ℝ)) := by
          rw [hp]
          ring
    · have hempty : fundamentalDiscriminantsBelow Y = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro D₀ hD₀
        obtain ⟨hD₀, hD₀Y⟩ := mem_fundamentalDiscriminantsBelow.mp hD₀
        have h5 := five_le_of_positiveQuadraticOrderDiscriminant
          (positiveQuadraticOrderDiscriminant_of_positiveFundamental hD₀)
        have h5real : (5 : ℝ) ≤ D₀ := by exact_mod_cast h5
        linarith
      change (∑ D₀ ∈ fundamentalDiscriminantsBelow Y, w (D₀ * f ^ 2)) ≤ _
      rw [hempty, Finset.sum_empty]
      positivity
  calc
    properOrderFormClassSum X ≤
        ∑ f ∈ Finset.Icc 1 ⌈X⌉₊,
          ∑ D₀ ∈ fundamentalDiscriminantsBelow (X / (f : ℝ) ^ 2), w (D₀ * f ^ 2) :=
      sum_orderDiscriminantsBelow_le_conductor_sum w hw X
    _ ≤ ∑ f ∈ Finset.Icc 1 ⌈X⌉₊, (A * C * K * classAverageScale X) *
        ((∑ d ∈ f.divisors, (d : ℝ)) / (f : ℝ) ^ (5 / 2 : ℝ)) :=
      Finset.sum_le_sum hinner
    _ = (A * C * K * classAverageScale X) *
        (∑ f ∈ Finset.Icc 1 ⌈X⌉₊,
          (∑ d ∈ f.divisors, (d : ℝ)) / (f : ℝ) ^ (5 / 2 : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (A * C * K * classAverageScale X) * B :=
      mul_le_mul_of_nonneg_left (hbudget _) (by positivity)
    _ = (A * C * K * B) * classAverageScale X := by ring

/-- The expanded headline follows from the two remaining mathematical
inputs: the actual conductor comparison and the uniform Pell exceptional
estimate. The selected-L second moment and conductor analytic transfer
are already proved; neither remaining input is claimed here. -/
theorem realQuadraticOrderClassAverageAssertion_of_uniformExceptional_conductorBound
    (A cSave : ℝ) (hA : 0 < A)
    (hconductor : ∀ D₀ f : ℕ, PositiveFundamentalDiscriminant D₀ → 0 < f →
      (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass ((D₀ * f ^ 2 : ℕ) : ℤ)) : ℝ) ≤
        A * (∑ d ∈ f.divisors, (d : ℝ)) *
          (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D₀ : ℤ)) : ℝ))
    (hUniform : UniformExceptionalEstimate cSave) :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_conductorBound A hA hconductor
    (realQuadraticFieldClassAverageAssertion_of_uniformExceptional cSave hUniform)

end
end PellPaper
