import Pell.CorollaryOddClassMain4WilsonPublishedInputs

/-!
# Combining the four published rectangle specializations

This module applies the triangle inequality to the four exact branch
prefixes.  It converts either published rectangle input into one bound for
the combined ordinary prefix appearing in the Abel majorant.  No analytic
input is proved or hidden here.
-/

namespace PellPaper

noncomputable section

/-- Sum of the four Wilson scales at the exact branch cutoffs. -/
def main4WilsonFourTwistRectangleScale (X : ℝ) (N : ℕ) : ℝ :=
  main4WilsonWeightedRectangleScale ⌈X⌉₊ N +
    main4WilsonWeightedRectangleScale ⌈X / 4⌉₊ N +
    main4WilsonWeightedRectangleScale ⌈X / 8⌉₊ N +
    main4WilsonWeightedRectangleScale ⌈X / 8⌉₊ N

/-- Sum of the four Friedlander--Iwaniec scales at the exact branch
cutoffs. -/
def main4FriedlanderIwaniecFourTwistRectangleScale
    (X : ℝ) (N : ℕ) : ℝ :=
  main4FriedlanderIwaniecRectangleScale ⌈X⌉₊ N +
    main4FriedlanderIwaniecRectangleScale ⌈X / 4⌉₊ N +
    main4FriedlanderIwaniecRectangleScale ⌈X / 8⌉₊ N +
    main4FriedlanderIwaniecRectangleScale ⌈X / 8⌉₊ N

/-- The initial combined prefix can be estimated at the admissible endpoint
`N = 2`; all four newly added even-index terms vanish. -/
theorem main4WilsonFourTwistPrefixSumAwayFromEight_one_eq_two (X : ℝ) :
    main4WilsonFourTwistPrefixSumAwayFromEight X 1 =
      main4WilsonFourTwistPrefixSumAwayFromEight X 2 := by
  unfold main4WilsonFourTwistPrefixSumAwayFromEight
  rw [main4WilsonWeightedTwistPrefix_one_eq_two,
    main4WilsonWeightedTwistPrefix_one_eq_two,
    main4WilsonWeightedTwistPrefix_one_eq_two,
    main4WilsonWeightedTwistPrefix_one_eq_two]

/-- Wilson's weighted estimate, once supplied, bounds the combined ordinary
prefix by the sum of its four exact branch scales. -/
theorem abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_of_wilsonRectangle
    {C X : ℝ} {N : ℕ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM₁ : 2 ≤ ⌈X⌉₊) (hM₄ : 2 ≤ ⌈X / 4⌉₊)
    (hM₈ : 2 ≤ ⌈X / 8⌉₊) (hN : 2 ≤ N) :
    |main4WilsonFourTwistPrefixSumAwayFromEight X N| ≤
      C * main4WilsonFourTwistRectangleScale X N := by
  let A := main4WilsonWeightedTwistPrefix 1
    (fun m ↦ 1 / (m.divisors.card : ℝ))
    (main4OddBranchRadicandsBelow X) N
  let B := main4WilsonWeightedTwistPrefix main4ChiFourModuloEight
    (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
    (main4FourBranchRadicandsBelow X) N
  let C₈ := main4WilsonWeightedTwistPrefix ZMod.χ₈
    (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
    (main4EightOneBranchRadicandsBelowAwayFromEight X) N
  let D₈ := main4WilsonWeightedTwistPrefix ZMod.χ₈'
    (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
    (main4EightThreeBranchRadicandsBelow X) N
  have hA : |A| ≤
      C * main4WilsonWeightedRectangleScale ⌈X⌉₊ N := by
    exact abs_main4WilsonOddBranchPrefix_le_of_wilsonRectangle
      hWilson hM₁ hN
  have hB : |B| ≤
      C * main4WilsonWeightedRectangleScale ⌈X / 4⌉₊ N := by
    exact abs_main4WilsonFourBranchPrefix_le_of_wilsonRectangle
      hWilson hM₄ hN
  have hC : |C₈| ≤
      C * main4WilsonWeightedRectangleScale ⌈X / 8⌉₊ N := by
    exact abs_main4WilsonEightOneBranchPrefixAwayFromEight_le_of_wilsonRectangle
      hWilson hM₈ hN
  have hD : |D₈| ≤
      C * main4WilsonWeightedRectangleScale ⌈X / 8⌉₊ N := by
    exact abs_main4WilsonEightThreeBranchPrefix_le_of_wilsonRectangle
      hWilson hM₈ hN
  have hAB := abs_add_le A B
  have hABC := abs_add_le (A + B) C₈
  have hABCD := abs_add_le (A + B + C₈) D₈
  change |A + B + C₈ + D₈| ≤ _
  unfold main4WilsonFourTwistRectangleScale
  linarith

/-- The Friedlander--Iwaniec estimate, once supplied, gives the companion
combined-prefix bound used above the Abel splitting point. -/
theorem
    abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_of_friedlanderIwaniecRectangle
    {C X : ℝ} {N : ℕ}
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith C)
    (hM₁ : 2 ≤ ⌈X⌉₊) (hM₄ : 2 ≤ ⌈X / 4⌉₊)
    (hM₈ : 2 ≤ ⌈X / 8⌉₊) (hN : 2 ≤ N) :
    |main4WilsonFourTwistPrefixSumAwayFromEight X N| ≤
      C * main4FriedlanderIwaniecFourTwistRectangleScale X N := by
  let A := main4WilsonWeightedTwistPrefix 1
    (fun m ↦ 1 / (m.divisors.card : ℝ))
    (main4OddBranchRadicandsBelow X) N
  let B := main4WilsonWeightedTwistPrefix main4ChiFourModuloEight
    (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
    (main4FourBranchRadicandsBelow X) N
  let C₈ := main4WilsonWeightedTwistPrefix ZMod.χ₈
    (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
    (main4EightOneBranchRadicandsBelowAwayFromEight X) N
  let D₈ := main4WilsonWeightedTwistPrefix ZMod.χ₈'
    (fun m ↦ 1 / (2 * (m.divisors.card : ℝ)))
    (main4EightThreeBranchRadicandsBelow X) N
  have hA : |A| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X⌉₊ N := by
    exact abs_main4WilsonOddBranchPrefix_le_of_friedlanderIwaniecRectangle
      hFI hM₁ hN
  have hB : |B| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X / 4⌉₊ N := by
    exact abs_main4WilsonFourBranchPrefix_le_of_friedlanderIwaniecRectangle
      hFI hM₄ hN
  have hC : |C₈| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X / 8⌉₊ N := by
    exact
      abs_main4WilsonEightOneBranchPrefixAwayFromEight_le_of_friedlanderIwaniecRectangle
        hFI hM₈ hN
  have hD : |D₈| ≤
      C * main4FriedlanderIwaniecRectangleScale ⌈X / 8⌉₊ N := by
    exact
      abs_main4WilsonEightThreeBranchPrefix_le_of_friedlanderIwaniecRectangle
        hFI hM₈ hN
  have hAB := abs_add_le A B
  have hABC := abs_add_le (A + B) C₈
  have hABCD := abs_add_le (A + B + C₈) D₈
  change |A + B + C₈ + D₈| ≤ _
  unfold main4FriedlanderIwaniecFourTwistRectangleScale
  linarith

end

end PellPaper
