import Pell.FundamentalDiscriminantPellBridge

/-!
# Positive discriminants of quadratic orders

The family in the manuscript, Theorem 1.1, includes all positive nonsquare
integers congruent to zero or one modulo four. Fundamental discriminants
form a subfamily. This module supplies the literal family and strict cutoff;
it does not identify any class number or assert an average estimate.
-/

namespace PellPaper

noncomputable section

/-- The arithmetic discriminant family in the manuscript, including nonmaximal
orders and excluding every square. -/
def PositiveQuadraticOrderDiscriminant (D : ℕ) : Prop :=
  0 < D ∧ ¬ IsSquare D ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- The smallest positive nonsquare quadratic discriminant is five. -/
theorem five_le_of_positiveQuadraticOrderDiscriminant {D : ℕ}
    (hD : PositiveQuadraticOrderDiscriminant D) : 5 ≤ D := by
  rcases hD with ⟨hpos, hns, hmod⟩
  by_contra h
  interval_cases D <;> norm_num at *
  exact hns ⟨2, rfl⟩

/-- Every positive fundamental discriminant belongs to the order family. -/
theorem positiveQuadraticOrderDiscriminant_of_positiveFundamental {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) :
    PositiveQuadraticOrderDiscriminant D := by
  refine ⟨by have := hD.1; omega,
    not_isSquare_of_positiveFundamentalDiscriminant hD, ?_⟩
  rcases hD.2 with ⟨_, hmod⟩ | ⟨d, rfl, _, _⟩
  · exact Or.inr hmod
  · exact Or.inl (by omega)

/-- All positive nonsquare quadratic discriminants with strict real cutoff. -/
def orderDiscriminantsBelow (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range ⌈X⌉₊).filter PositiveQuadraticOrderDiscriminant

@[simp]
theorem mem_orderDiscriminantsBelow {D : ℕ} {X : ℝ} :
    D ∈ orderDiscriminantsBelow X ↔
      PositiveQuadraticOrderDiscriminant D ∧ (D : ℝ) < X := by
  simp [orderDiscriminantsBelow, Nat.lt_ceil, and_comm]

theorem orderDiscriminantsBelow_mono {X Y : ℝ} (hXY : X ≤ Y) :
    orderDiscriminantsBelow X ⊆ orderDiscriminantsBelow Y := by
  intro D hD
  obtain ⟨hD, hDX⟩ := mem_orderDiscriminantsBelow.mp hD
  exact mem_orderDiscriminantsBelow.mpr ⟨hD, hDX.trans_le hXY⟩

/-- The previously formalized family is contained in the broader family at
the same strict cutoff. -/
theorem fundamentalDiscriminantsBelow_subset_orderDiscriminantsBelow (X : ℝ) :
    fundamentalDiscriminantsBelow X ⊆ orderDiscriminantsBelow X := by
  intro D hD
  obtain ⟨hD, hDX⟩ := mem_fundamentalDiscriminantsBelow.mp hD
  exact mem_orderDiscriminantsBelow.mpr
    ⟨positiveQuadraticOrderDiscriminant_of_positiveFundamental hD, hDX⟩

end
end PellPaper
