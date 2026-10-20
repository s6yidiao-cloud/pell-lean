import Pell.CorollaryOddClassMain4WilsonCombinedPrefix

/-!
# Low/high Abel synthesis from the two published rectangle inputs

This module carries out the finite synthesis described in the manuscript.
The Abel kernel is split at the natural ceiling of `sqrt X`.  Wilson's
weighted rectangle estimate controls the lower part; the
Friedlander--Iwaniec rectangle estimate controls the upper part and the
terminal prefix at the exact truncation endpoint `ceil(X)^2`.

The only hypotheses are the two source-level rectangle estimates (with
their constants displayed) and an elementary lower bound on `X`.  No
asymptotic absorption estimate is assumed or asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-! ## The exact finite split -/

/-- The natural integer realization of the split at `sqrt X`. -/
def main4WilsonAbelSplitPoint (X : ℝ) : ℕ :=
  ⌈Real.sqrt X⌉₊

/-- The part of the Abel majorant at prefix lengths at most `ceil(sqrt X)`.
The prefix of length one is retained literally here. -/
def main4WilsonLowAbelPrefixMajorantAwayFromEight (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  ∑ j ∈ (Finset.range (N - 1)).filter (fun j ↦ j + 1 ≤ S),
    |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
      (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))

/-- The part of the Abel majorant strictly above `ceil(sqrt X)`, together
with the terminal prefix at the exact endpoint `ceil(X)^2`. -/
def main4WilsonHighAbelPrefixMajorantAwayFromEight (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  |main4WilsonFourTwistPrefixSumAwayFromEight X N| / (N : ℝ) +
    ∑ j ∈ (Finset.range (N - 1)).filter (fun j ↦ ¬j + 1 ≤ S),
      |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
        (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))

/-- Exact decomposition of the existing Abel majorant into its low and
high source ranges. -/
theorem main4WilsonFourTwistAbelMajorantAwayFromEight_eq_low_add_high
    (X : ℝ) :
    main4WilsonFourTwistAbelMajorantAwayFromEight X =
      main4WilsonLowAbelPrefixMajorantAwayFromEight X +
        main4WilsonHighAbelPrefixMajorantAwayFromEight X := by
  let N := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  let F : ℕ → ℝ := fun j ↦
    |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
      (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))
  unfold main4WilsonFourTwistAbelMajorantAwayFromEight
    main4WilsonLowAbelPrefixMajorantAwayFromEight
    main4WilsonHighAbelPrefixMajorantAwayFromEight
  dsimp only
  change
    |main4WilsonFourTwistPrefixSumAwayFromEight X N| / (N : ℝ) +
        ∑ j ∈ Finset.range (N - 1), F j =
      (∑ j ∈ (Finset.range (N - 1)).filter (fun j ↦ j + 1 ≤ S), F j) +
        (|main4WilsonFourTwistPrefixSumAwayFromEight X N| / (N : ℝ) +
          ∑ j ∈ (Finset.range (N - 1)).filter (fun j ↦ ¬j + 1 ≤ S),
            F j)
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range (N - 1)) (fun j ↦ j + 1 ≤ S) F]
  ring

/-! ## Explicit sums of the two published scales -/

/-- The exact sum of Wilson scales used below the splitting point.  The
`max 2` records the admissible endpoint used for the length-one prefix. -/
def main4WilsonLowAbelRectangleScale (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  ∑ j ∈ (Finset.range (N - 1)).filter (fun j ↦ j + 1 ≤ S),
    main4WilsonFourTwistRectangleScale X (max 2 (j + 1)) /
      (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))

/-- The exact Friedlander--Iwaniec scale sum above the splitting point,
including the terminal endpoint `ceil(X)^2`. -/
def main4FriedlanderIwaniecHighAbelRectangleScale (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  let S := main4WilsonAbelSplitPoint X
  main4FriedlanderIwaniecFourTwistRectangleScale X N / (N : ℝ) +
    ∑ j ∈ (Finset.range (N - 1)).filter (fun j ↦ ¬j + 1 ≤ S),
      main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
        (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))

/-! ## Endpoint admissibility -/

theorem main4Wilson_outerEndpoints_admissible {X : ℝ} (hX : 16 ≤ X) :
    2 ≤ ⌈X⌉₊ ∧ 2 ≤ ⌈X / 4⌉₊ ∧ 2 ≤ ⌈X / 8⌉₊ := by
  have h₁ : (2 : ℝ) ≤ X := by linarith
  have h₄ : (2 : ℝ) ≤ X / 4 := by linarith
  have h₈ : (2 : ℝ) ≤ X / 8 := by linarith
  constructor
  · exact_mod_cast h₁.trans (Nat.le_ceil X)
  constructor
  · exact_mod_cast h₄.trans (Nat.le_ceil (X / 4))
  · exact_mod_cast h₈.trans (Nat.le_ceil (X / 8))

theorem main4WilsonAbelSplitPoint_two_le {X : ℝ} (hX : 16 ≤ X) :
    2 ≤ main4WilsonAbelSplitPoint X := by
  have hX0 : 0 ≤ X := by linarith
  have hsqrt : (2 : ℝ) ≤ Real.sqrt X := by
    have hsquare := Real.sq_sqrt hX0
    nlinarith [Real.sqrt_nonneg X]
  unfold main4WilsonAbelSplitPoint
  exact_mod_cast hsqrt.trans (Nat.le_ceil (Real.sqrt X))

theorem main4Wilson_terminalEndpoint_two_le {X : ℝ} (hX : 16 ≤ X) :
    2 ≤ ⌈X⌉₊ ^ 2 := by
  have hceil := (main4Wilson_outerEndpoints_admissible hX).1
  calc
    2 ≤ 2 ^ 2 := by norm_num
    _ ≤ ⌈X⌉₊ ^ 2 := by gcongr

/-! ## Low and high rectangle estimates inside the Abel kernel -/

/-- Wilson's estimate applies to every positive prefix after replacing the
sole inadmissible length `1` by the equal length-`2` prefix. -/
theorem abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_wilson_max_two
    {C X : ℝ} {t : ℕ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM₁ : 2 ≤ ⌈X⌉₊) (hM₄ : 2 ≤ ⌈X / 4⌉₊)
    (hM₈ : 2 ≤ ⌈X / 8⌉₊) (ht : 1 ≤ t) :
    |main4WilsonFourTwistPrefixSumAwayFromEight X t| ≤
      C * main4WilsonFourTwistRectangleScale X (max 2 t) := by
  by_cases ht₂ : 2 ≤ t
  · rw [max_eq_right ht₂]
    exact abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_of_wilsonRectangle
      hWilson hM₁ hM₄ hM₈ ht₂
  · have htOne : t = 1 := by omega
    subst t
    rw [main4WilsonFourTwistPrefixSumAwayFromEight_one_eq_two]
    simpa using
      abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_of_wilsonRectangle
        hWilson hM₁ hM₄ hM₈ (by norm_num : 2 ≤ (2 : ℕ))

/-- Wilson's weighted rectangle estimate controls the complete low part of
the finite Abel kernel. -/
theorem main4WilsonLowAbelPrefixMajorantAwayFromEight_le
    {C X : ℝ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith C)
    (hM₁ : 2 ≤ ⌈X⌉₊) (hM₄ : 2 ≤ ⌈X / 4⌉₊)
    (hM₈ : 2 ≤ ⌈X / 8⌉₊) :
    main4WilsonLowAbelPrefixMajorantAwayFromEight X ≤
      C * main4WilsonLowAbelRectangleScale X := by
  unfold main4WilsonLowAbelPrefixMajorantAwayFromEight
    main4WilsonLowAbelRectangleScale
  dsimp only
  calc
    (∑ j ∈ (Finset.range (⌈X⌉₊ ^ 2 - 1)).filter
          (fun j ↦ j + 1 ≤ main4WilsonAbelSplitPoint X),
        |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
          (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))) ≤
        ∑ j ∈ (Finset.range (⌈X⌉₊ ^ 2 - 1)).filter
          (fun j ↦ j + 1 ≤ main4WilsonAbelSplitPoint X),
          (C * main4WilsonFourTwistRectangleScale X (max 2 (j + 1))) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_wilson_max_two
          hWilson hM₁ hM₄ hM₈ (by omega))
        (by positivity)
    _ = C *
        ∑ j ∈ (Finset.range (⌈X⌉₊ ^ 2 - 1)).filter
          (fun j ↦ j + 1 ≤ main4WilsonAbelSplitPoint X),
          main4WilsonFourTwistRectangleScale X (max 2 (j + 1)) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The Friedlander--Iwaniec estimate controls the terminal prefix and all
prefixes strictly above the splitting point. -/
theorem main4WilsonHighAbelPrefixMajorantAwayFromEight_le
    {C X : ℝ}
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith C)
    (hM₁ : 2 ≤ ⌈X⌉₊) (hM₄ : 2 ≤ ⌈X / 4⌉₊)
    (hM₈ : 2 ≤ ⌈X / 8⌉₊)
    (hSplit : 2 ≤ main4WilsonAbelSplitPoint X)
    (hTerminal : 2 ≤ ⌈X⌉₊ ^ 2) :
    main4WilsonHighAbelPrefixMajorantAwayFromEight X ≤
      C * main4FriedlanderIwaniecHighAbelRectangleScale X := by
  unfold main4WilsonHighAbelPrefixMajorantAwayFromEight
    main4FriedlanderIwaniecHighAbelRectangleScale
  dsimp only
  have hTerm :=
    abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_of_friedlanderIwaniecRectangle
      hFI hM₁ hM₄ hM₈ hTerminal
  calc
    |main4WilsonFourTwistPrefixSumAwayFromEight X (⌈X⌉₊ ^ 2)| /
          ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) +
        ∑ j ∈ (Finset.range (⌈X⌉₊ ^ 2 - 1)).filter
          (fun j ↦ ¬j + 1 ≤ main4WilsonAbelSplitPoint X),
          |main4WilsonFourTwistPrefixSumAwayFromEight X (j + 1)| /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) ≤
        (C * main4FriedlanderIwaniecFourTwistRectangleScale X
          (⌈X⌉₊ ^ 2)) / ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) +
        ∑ j ∈ (Finset.range (⌈X⌉₊ ^ 2 - 1)).filter
          (fun j ↦ ¬j + 1 ≤ main4WilsonAbelSplitPoint X),
          (C * main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1)) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hTerm (by positivity)
      · apply Finset.sum_le_sum
        intro j hj
        have hjAbove : ¬j + 1 ≤ main4WilsonAbelSplitPoint X :=
          (Finset.mem_filter.mp hj).2
        have hjTwo : 2 ≤ j + 1 := by omega
        exact div_le_div_of_nonneg_right
          (abs_main4WilsonFourTwistPrefixSumAwayFromEight_le_of_friedlanderIwaniecRectangle
            hFI hM₁ hM₄ hM₈ hjTwo)
          (by positivity)
    _ = C *
        (main4FriedlanderIwaniecFourTwistRectangleScale X (⌈X⌉₊ ^ 2) /
          ((⌈X⌉₊ ^ 2 : ℕ) : ℝ) +
        ∑ j ∈ (Finset.range (⌈X⌉₊ ^ 2 - 1)).filter
          (fun j ↦ ¬j + 1 ≤ main4WilsonAbelSplitPoint X),
          main4FriedlanderIwaniecFourTwistRectangleScale X (j + 1) /
            (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        ring

/-! ## Complete finite synthesis -/

/-- The two published rectangle estimates imply the exact low/high bound
for the Abel majorant, with no further analytic hypothesis. -/
theorem main4WilsonFourTwistAbelMajorantAwayFromEight_le_low_high_scales
    {Cw Cf X : ℝ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith Cw)
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith Cf)
    (hX : 16 ≤ X) :
    main4WilsonFourTwistAbelMajorantAwayFromEight X ≤
      Cw * main4WilsonLowAbelRectangleScale X +
        Cf * main4FriedlanderIwaniecHighAbelRectangleScale X := by
  obtain ⟨hM₁, hM₄, hM₈⟩ := main4Wilson_outerEndpoints_admissible hX
  rw [main4WilsonFourTwistAbelMajorantAwayFromEight_eq_low_add_high]
  exact add_le_add
    (main4WilsonLowAbelPrefixMajorantAwayFromEight_le
      hWilson hM₁ hM₄ hM₈)
    (main4WilsonHighAbelPrefixMajorantAwayFromEight_le
      hFI hM₁ hM₄ hM₈
        (main4WilsonAbelSplitPoint_two_le hX)
        (main4Wilson_terminalEndpoint_two_le hX))

/-- Consequently the original signed four-twist reciprocal polynomial at
the exact endpoint `ceil(X)^2` is bounded by the same explicit low/high
scale sum. -/
theorem main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight_le_low_high_scales
    {Cw Cf X : ℝ}
    (hWilson : Main4WilsonWeightedRectangleEstimateWith Cw)
    (hFI : Main4FriedlanderIwaniecRectangleEstimateWith Cf)
    (hX : 16 ≤ X) :
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X ≤
      Cw * main4WilsonLowAbelRectangleScale X +
        Cf * main4FriedlanderIwaniecHighAbelRectangleScale X := by
  exact le_trans
    (main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight_le_abelMajorant
      (by linarith))
    (main4WilsonFourTwistAbelMajorantAwayFromEight_le_low_high_scales
      hWilson hFI hX)

end

end PellPaper
