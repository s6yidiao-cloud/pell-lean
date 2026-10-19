import Pell.CorollaryOddClassMain4WilsonDivisorWeight

/-!
# Source-faithful rectangle inputs for Wilson's weighted moment

This module names the two published analytic rectangle interfaces used in
the manuscript: Wilson's Theorem 1.1 specialized to
`f(m) = 1 / tau(m)`, `alpha = 1/2`, and `epsilon = 1/6`, and the
Friedlander--Iwaniec estimate (1.3).  Both are real specializations of the
published complex-sequence statements and retain uniform quantification over
the bounded odd-supported coefficient sequences.

The conditional adapter theorems below merely instantiate these two exact
inputs with the four already verified branch masks.  No analytic input is
inhabited in this module; the FI interface is discharged downstream by the
formal reconstruction of its proof.  We use Wilson's Theorem 1.1 directly and
therefore do not rely on the inconsistent `mu^2(q m m_1)` spelling in the
statement of Wilson's Lemma 4.1; its proof (4.1) instead has the intended
`mu^2(2 m m_1)`.
-/

namespace PellPaper

noncomputable section

/-- The coefficient conditions shared by Wilson's Theorem 1.1 and the
Friedlander--Iwaniec estimate. -/
def main4OddSupportedUnitBound (a : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, Even n → a n = 0) ∧ ∀ n : ℕ, |a n| ≤ 1

theorem main4WilsonTwistSequence_oddSupportedUnitBound
    (rho : DirichletCharacter ℤ 8) :
    main4OddSupportedUnitBound (main4WilsonTwistSequence rho) := by
  exact ⟨main4WilsonTwistSequence_eq_zero_of_even rho,
    abs_main4WilsonTwistSequence_le_one rho⟩

theorem main4WilsonOddBranchMask_oddSupportedUnitBound (X : ℝ) :
    main4OddSupportedUnitBound (main4WilsonOddBranchMask X) := by
  exact ⟨main4WilsonOddBranchMask_eq_zero_of_even X,
    abs_main4WilsonOddBranchMask_le_one X⟩

theorem main4WilsonFourBranchMask_oddSupportedUnitBound (X : ℝ) :
    main4OddSupportedUnitBound (main4WilsonFourBranchMask X) := by
  exact ⟨main4WilsonFourBranchMask_eq_zero_of_even X,
    abs_main4WilsonFourBranchMask_le_one X⟩

theorem main4WilsonEightOneBranchMaskAwayFromEight_oddSupportedUnitBound
    (X : ℝ) :
    main4OddSupportedUnitBound
      (main4WilsonEightOneBranchMaskAwayFromEight X) := by
  exact ⟨main4WilsonEightOneBranchMaskAwayFromEight_eq_zero_of_even X,
    abs_main4WilsonEightOneBranchMaskAwayFromEight_le_one X⟩

theorem main4WilsonEightThreeBranchMask_oddSupportedUnitBound (X : ℝ) :
    main4OddSupportedUnitBound (main4WilsonEightThreeBranchMask X) := by
  exact ⟨main4WilsonEightThreeBranchMask_eq_zero_of_even X,
    abs_main4WilsonEightThreeBranchMask_le_one X⟩

theorem main4WilsonOddBranchCoefficient_oddSupportedUnitBound (X : ℝ) :
    main4OddSupportedUnitBound (main4WilsonOddBranchCoefficient X) := by
  exact ⟨main4WilsonOddBranchCoefficient_eq_zero_of_even X,
    abs_main4WilsonOddBranchCoefficient_le_one X⟩

theorem main4WilsonFourBranchCoefficient_oddSupportedUnitBound (X : ℝ) :
    main4OddSupportedUnitBound (main4WilsonFourBranchCoefficient X) := by
  exact ⟨main4WilsonFourBranchCoefficient_eq_zero_of_even X,
    abs_main4WilsonFourBranchCoefficient_le_one X⟩

theorem
    main4WilsonEightOneBranchCoefficientAwayFromEight_oddSupportedUnitBound
    (X : ℝ) :
    main4OddSupportedUnitBound
      (main4WilsonEightOneBranchCoefficientAwayFromEight X) := by
  exact
    ⟨main4WilsonEightOneBranchCoefficientAwayFromEight_eq_zero_of_even X,
      abs_main4WilsonEightOneBranchCoefficientAwayFromEight_le_one X⟩

theorem main4WilsonEightThreeBranchCoefficient_oddSupportedUnitBound
    (X : ℝ) :
    main4OddSupportedUnitBound (main4WilsonEightThreeBranchCoefficient X) := by
  exact ⟨main4WilsonEightThreeBranchCoefficient_eq_zero_of_even X,
    abs_main4WilsonEightThreeBranchCoefficient_le_one X⟩

/-- The first ordinary prefix may be estimated with Wilson's admissible
endpoint `N = 2`: the added `n = 2` term vanishes because every modulus-eight
twist is supported on odd integers.  This accounts explicitly for the
initial term hidden when Wilson's display (4.2) starts its integral at `2`. -/
theorem main4WilsonWeightedTwistPrefix_one_eq_two
    (rho : DirichletCharacter ℤ 8) (weight : ℕ → ℝ) (s : Finset ℕ) :
    main4WilsonWeightedTwistPrefix rho weight s 1 =
      main4WilsonWeightedTwistPrefix rho weight s 2 := by
  unfold main4WilsonWeightedTwistPrefix
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [show Finset.Icc 1 2 = insert 2 (Finset.Icc 1 1) by decide,
    Finset.sum_insert (by decide)]
  rw [show main4WilsonTwistCoefficient rho m 2 = 0 by
    unfold main4WilsonTwistCoefficient
    rw [dirichletCharacter_mod_eight_apply_eq_zero_of_even rho 2 (by norm_num)]
    norm_num, zero_add]

/-! ## The two published analytic estimates -/

/-- The exact scale in Wilson's Theorem 1.1 after setting
`alpha = 1/2` and `epsilon = 1/6`. -/
def main4WilsonWeightedRectangleScale (M N : ℕ) : ℝ :=
  (M : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) /
      Real.sqrt (Real.log (M : ℝ)) +
    (M : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (3 / 2 : ℝ) *
      Real.sqrt (Real.log (N : ℝ)) /
        (Real.log (M : ℝ)) ^ (1 / 4 : ℝ)

/-- Wilson's weighted quadratic rectangle conclusion with its constant made
explicit.  This is a named external analytic interface, not a theorem
asserted by this project. -/
def Main4WilsonWeightedRectangleEstimateWith (C : ℝ) : Prop :=
  ∀ (M N : ℕ), 2 ≤ M → 2 ≤ N →
    ∀ (a b : ℕ → ℝ),
      main4OddSupportedUnitBound a →
      main4OddSupportedUnitBound b →
      |main4OrdinaryJacobiRectangle a
          (fun m ↦ b m * main4WilsonReciprocalDivisorWeight m) M N| ≤
        C * main4WilsonWeightedRectangleScale M N

/-- Source-level existential form of the specialized Wilson estimate. -/
def Main4WilsonWeightedRectangleEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ Main4WilsonWeightedRectangleEstimateWith C

/-- The exact Friedlander--Iwaniec scale in Wilson's display (1.3). -/
def main4FriedlanderIwaniecRectangleScale (M N : ℕ) : ℝ :=
  (M : ℝ) * (N : ℝ) *
    ((N : ℝ) ^ (-1 / 6 : ℝ) + (M : ℝ) ^ (-1 / 6 : ℝ)) *
      (Real.log (3 * (M : ℝ) * (N : ℝ))) ^ (7 / 6 : ℝ)

/-- Friedlander--Iwaniec (1.3), restricted from arbitrary complex
coefficients to real coefficients.  This source-shaped interface is inhabited
in `CorollaryOddClassMain4FriedlanderIwaniecProved`. -/
def Main4FriedlanderIwaniecRectangleEstimateWith (C : ℝ) : Prop :=
  ∀ (M N : ℕ), 2 ≤ M → 2 ≤ N →
    ∀ (a b : ℕ → ℝ),
      main4OddSupportedUnitBound a →
      main4OddSupportedUnitBound b →
      |main4OrdinaryJacobiRectangle a b M N| ≤
        C * main4FriedlanderIwaniecRectangleScale M N

/-- Source-level existential form of Friedlander--Iwaniec (1.3). -/
def Main4FriedlanderIwaniecRectangleEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ Main4FriedlanderIwaniecRectangleEstimateWith C

/-! ## Exact specializations to the four prefixes -/

theorem abs_main4WilsonOddBranchPrefix_le_of_wilsonRectangle
    {C X : ℝ} {N : ℕ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix 1
        (fun m ↦ 1 / (m.divisors.card : ℝ))
        (main4OddBranchRadicandsBelow X) N| ≤
      C * main4WilsonWeightedRectangleScale ⌈X⌉₊ N := by
  rw [main4WilsonOddBranchPrefix_eq_ordinaryRectangle]
  unfold main4WilsonOddBranchCoefficient
  exact hWilson ⌈X⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound 1)
    (main4WilsonOddBranchMask_oddSupportedUnitBound X)

theorem abs_main4WilsonFourBranchPrefix_le_of_wilsonRectangle
    {C X : ℝ} {N : ℕ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X / 4⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix main4ChiFourModuloEight
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4FourBranchRadicandsBelow X) N| ≤
      C * main4WilsonWeightedRectangleScale ⌈X / 4⌉₊ N := by
  rw [main4WilsonFourBranchPrefix_eq_ordinaryRectangle]
  unfold main4WilsonFourBranchCoefficient
  exact hWilson ⌈X / 4⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound
      main4ChiFourModuloEight)
    (main4WilsonFourBranchMask_oddSupportedUnitBound X)

theorem abs_main4WilsonEightOneBranchPrefixAwayFromEight_le_of_wilsonRectangle
    {C X : ℝ} {N : ℕ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X / 8⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix ZMod.χ₈
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4EightOneBranchRadicandsBelowAwayFromEight X) N| ≤
      C * main4WilsonWeightedRectangleScale ⌈X / 8⌉₊ N := by
  rw [main4WilsonEightOneBranchPrefixAwayFromEight_eq_ordinaryRectangle]
  unfold main4WilsonEightOneBranchCoefficientAwayFromEight
  exact hWilson ⌈X / 8⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound ZMod.χ₈)
    (main4WilsonEightOneBranchMaskAwayFromEight_oddSupportedUnitBound X)

theorem abs_main4WilsonEightThreeBranchPrefix_le_of_wilsonRectangle
    {C X : ℝ} {N : ℕ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X / 8⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix ZMod.χ₈'
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4EightThreeBranchRadicandsBelow X) N| ≤
      C * main4WilsonWeightedRectangleScale ⌈X / 8⌉₊ N := by
  rw [main4WilsonEightThreeBranchPrefix_eq_ordinaryRectangle]
  unfold main4WilsonEightThreeBranchCoefficient
  exact hWilson ⌈X / 8⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound ZMod.χ₈')
    (main4WilsonEightThreeBranchMask_oddSupportedUnitBound X)

theorem abs_main4WilsonOddBranchPrefix_le_of_friedlanderIwaniecRectangle
    {C X : ℝ} {N : ℕ}
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix 1
        (fun m ↦ 1 / (m.divisors.card : ℝ))
        (main4OddBranchRadicandsBelow X) N| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X⌉₊ N := by
  rw [main4WilsonOddBranchPrefix_eq_ordinaryRectangle]
  exact hFI ⌈X⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound 1)
    (main4WilsonOddBranchCoefficient_oddSupportedUnitBound X)

theorem abs_main4WilsonFourBranchPrefix_le_of_friedlanderIwaniecRectangle
    {C X : ℝ} {N : ℕ}
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X / 4⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix main4ChiFourModuloEight
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4FourBranchRadicandsBelow X) N| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X / 4⌉₊ N := by
  rw [main4WilsonFourBranchPrefix_eq_ordinaryRectangle]
  exact hFI ⌈X / 4⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound
      main4ChiFourModuloEight)
    (main4WilsonFourBranchCoefficient_oddSupportedUnitBound X)

theorem
    abs_main4WilsonEightOneBranchPrefixAwayFromEight_le_of_friedlanderIwaniecRectangle
    {C X : ℝ} {N : ℕ}
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X / 8⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix ZMod.χ₈
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4EightOneBranchRadicandsBelowAwayFromEight X) N| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X / 8⌉₊ N := by
  rw [main4WilsonEightOneBranchPrefixAwayFromEight_eq_ordinaryRectangle]
  exact hFI ⌈X / 8⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound ZMod.χ₈)
    (main4WilsonEightOneBranchCoefficientAwayFromEight_oddSupportedUnitBound X)

theorem abs_main4WilsonEightThreeBranchPrefix_le_of_friedlanderIwaniecRectangle
    {C X : ℝ} {N : ℕ}
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith C)
    (hM : 2 ≤ ⌈X / 8⌉₊) (hN : 2 ≤ N) :
    |main4WilsonWeightedTwistPrefix ZMod.χ₈'
        (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
        (main4EightThreeBranchRadicandsBelow X) N| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X / 8⌉₊ N := by
  rw [main4WilsonEightThreeBranchPrefix_eq_ordinaryRectangle]
  exact hFI ⌈X / 8⌉₊ N hM hN _ _
    (main4WilsonTwistSequence_oddSupportedUnitBound ZMod.χ₈')
    (main4WilsonEightThreeBranchCoefficient_oddSupportedUnitBound X)

end

end PellPaper
