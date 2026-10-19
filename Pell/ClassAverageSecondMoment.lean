import Pell.ClassAverageTargetConditional

/-!
# Removing the independent first moment from the class-average inputs

The positive fundamental discriminants below a real cutoff `X` form a subset
of the integers in `[1, floor X]`.  Their cardinality is therefore at most
`X` when `X ≥ 0`, with the original strict cutoff `D < X` unchanged.
Cauchy--Schwarz then turns a second-moment bound `Cmoment * X` into the
first-moment bound `sqrt Cmoment * X` needed by the class-average pipeline.

The final theorem is conditional.  It supplies neither an arithmetic class
number model nor the second moment, regulator comparison, or exceptional
cardinality estimate.
-/

namespace PellPaper

open Set
open scoped BigOperators

noncomputable section

/-- The discriminant family has at most `floor X` elements.  Passing to the
closed integer interval here only enlarges the original strict-cutoff family. -/
theorem fundamentalDiscriminantsBelow_card_le_floor (X : ℝ) :
    (fundamentalDiscriminantsBelow X).card ≤ ⌊X⌋₊ := by
  have hsubset : fundamentalDiscriminantsBelow X ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro D hD
    obtain ⟨hfund, hDX⟩ := mem_fundamentalDiscriminantsBelow.mp hD
    exact Finset.mem_Icc.mpr ⟨by have := hfund.1; omega, Nat.le_floor hDX.le⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsubset

/-- A real cardinality bound without a ceiling error at nonintegral cutoffs. -/
theorem fundamentalDiscriminantsBelow_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((fundamentalDiscriminantsBelow X).card : ℝ) ≤ X := by
  exact (Nat.cast_le.mpr (fundamentalDiscriminantsBelow_card_le_floor X)).trans
    (Nat.floor_le hX)

/-- An ambient linear second moment implies a linear first moment with the
explicit square-root constant.  The weights need not be nonnegative. -/
theorem fundamentalDiscriminantsBelow_first_moment_of_second_moment
    (L : ℕ → ℝ) {Cmoment X : ℝ} (hCmoment : 0 ≤ Cmoment) (hX : 0 ≤ X)
    (hsecond : (∑ D ∈ fundamentalDiscriminantsBelow X, (L D) ^ 2) ≤ Cmoment * X) :
    (∑ D ∈ fundamentalDiscriminantsBelow X, L D) ≤ Real.sqrt Cmoment * X := by
  apply exceptional_sum_le_of_product_le_sq
    (fundamentalDiscriminantsBelow X) (fundamentalDiscriminantsBelow X) L
    X (Cmoment * X) (Real.sqrt Cmoment * X) (by rfl)
    (fundamentalDiscriminantsBelow_card_le hX) hsecond
  · positivity
  · rw [mul_pow, Real.sq_sqrt hCmoment]
    nlinarith

/-- The exact all-cutoff class-average target follows from the old Cauchy
inputs with the independent first moment removed.  Its coefficient is now
forced to be `sqrt Cmoment`; every remaining input is still explicit. -/
theorem fieldClassAverageAssertion_of_secondMomentInputs
    (M : ClassNumberModel) (L r : ℕ → ℝ)
    (Ccard Cmoment r₀ a c Bsmall : ℝ)
    (hCcard : 0 ≤ Ccard) (hCmoment : 0 ≤ Cmoment)
    (hr₀ : 0 < r₀) (ha : 0 < a) (hc : 0 < c) (hBsmall : 0 ≤ Bsmall)
    (hL : ∀ D, PositiveFundamentalDiscriminant D → 0 ≤ L D)
    (hr : ∀ D, PositiveFundamentalDiscriminant D → r₀ ≤ r D)
    (hcutoff : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
      r₀ ≤ classAverageCutoff c X)
    (hpoint : ∀ X : ℝ, ∀ D ∈ fundamentalDiscriminantsBelow X,
      (M.formClassNumber D : ℝ) ≤
        (Real.sqrt X / Real.log X) * (L D / r D))
    (hsecond : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
      (∑ D ∈ fundamentalDiscriminantsBelow X, (L D) ^ 2) ≤ Cmoment * X)
    (hcard : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
      ∀ θ ∈ Icc r₀ (classAverageCutoff c X),
        (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < θ)).card : ℝ) ≤
          Ccard * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2))
    (hsmall : ∀ X : ℝ, 3 ≤ X → X ≤ Real.exp (Real.exp 1) →
      M.formClassSum X ≤ Bsmall * classAverageScale X) :
    FieldClassAverageAssertion M := by
  apply fieldClassAverageAssertion_of_cauchyInputs M
  exact
    { L := L
      r := r
      B₀ := Real.sqrt Cmoment
      Ccard := Ccard
      Cmoment := Cmoment
      r₀ := r₀
      a := a
      c := c
      Bsmall := Bsmall
      B₀_nonneg := Real.sqrt_nonneg _
      Ccard_nonneg := hCcard
      Cmoment_nonneg := hCmoment
      r₀_pos := hr₀
      a_pos := ha
      c_pos := hc
      Bsmall_nonneg := hBsmall
      L_nonneg := hL
      regulator_lower := hr
      cutoff_lower := hcutoff
      pointwise := hpoint
      first_moment := fun X hX ↦
        fundamentalDiscriminantsBelow_first_moment_of_second_moment L hCmoment
          ((Real.exp_pos _).le.trans hX) (hsecond X hX)
      second_moment := hsecond
      exceptional_cardinality := hcard
      small_range := hsmall }

end

end PellPaper
