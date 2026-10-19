import Pell.QuadraticOrderDiscriminants
import Pell.RealQuadraticFieldClassAverageConditional

/-!
# The all-order class-number target

The middle sum runs over every positive nonsquare order discriminant and
uses the existing literal proper-form quotient. The field sum retains the
actual field isomorphism classes. Finiteness of every form quotient is part
of the acceptance contract, since `Nat.card` alone is zero on infinite types.

The first displayed inequality transfers from the fundamental subfamily.
The upper bound and nonfundamental finiteness are proved by the unconditional
capstone in `Pell.Main3ElementaryFinalAssembly`.
-/

namespace PellPaper

noncomputable section

/-- The literal proper-form sum for the whole order-discriminant family. -/
def properOrderFormClassSum (X : ℝ) : ℝ :=
  ∑ D ∈ orderDiscriminantsBelow X,
    (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ)

theorem properOrderFormClassSum_nonneg (X : ℝ) :
    0 ≤ properOrderFormClassSum X :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem properOrderFormClassSum_mono {X Y : ℝ} (hXY : X ≤ Y) :
    properOrderFormClassSum X ≤ properOrderFormClassSum Y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (orderDiscriminantsBelow_mono hXY)
  intro D _ _
  exact Nat.cast_nonneg _

/-- The actual form sum from `main.tex` is a subfamily of the form sum in
the manuscript, with identical class weights and strict cutoff. -/
theorem fundamentalProperFormClassSum_le_orderFormClassSum (X : ℝ) :
    (∑ D ∈ fundamentalDiscriminantsBelow X,
      (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ)) ≤
      properOrderFormClassSum X := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fundamentalDiscriminantsBelow_subset_orderDiscriminantsBelow X)
  intro D _ _
  exact Nat.cast_nonneg _

/-- The first inequality of the expanded theorem, for every real cutoff. -/
theorem realQuadraticFieldClassSum_le_orderFormClassSum (X : ℝ) :
    realQuadraticFieldClassSum X ≤ properOrderFormClassSum X :=
  (realQuadraticFieldClassSum_le_properFormClassSum X).trans
    (fundamentalProperFormClassSum_le_orderFormClassSum X)

/-- A strengthening of `paper/main.tex`'s `T:field-class-average` to all
positive nonsquare order discriminants, together with finiteness of their
proper-form quotients. The constant precedes all real cutoffs at least three. -/
def RealQuadraticOrderClassAverageAssertion : Prop :=
  (∀ D : ℕ, PositiveQuadraticOrderDiscriminant D →
    Finite (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ))) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    realQuadraticFieldClassSum X ≤ properOrderFormClassSum X ∧
      properOrderFormClassSum X ≤ C * classAverageScale X

/-- The expanded theorem implies the previously specified fundamental-only
theorem. The stronger upper bound remains the caller's explicit premise. -/
theorem RealQuadraticOrderClassAverageAssertion.to_fundamental
    (h : RealQuadraticOrderClassAverageAssertion) :
    RealQuadraticFieldClassAverageAssertion := by
  obtain ⟨_, C, hC, hbound⟩ := h
  refine ⟨C, hC, fun X hX => ⟨realQuadraticFieldClassSum_le_properFormClassSum X, ?_⟩⟩
  exact (fundamentalProperFormClassSum_le_orderFormClassSum X).trans (hbound X hX).2

end
end PellPaper
