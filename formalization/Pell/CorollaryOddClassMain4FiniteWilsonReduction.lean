import Pell.CorollaryOddClassMain4DiscriminantDecomposition
import Pell.CorollaryOddClassMain4QuadraticCharacterBranches
import Pell.CorollaryOddClassMain4LValueTruncation
import Pell.CorollaryOddClassMain4WeightedMomentBridge

/-!
# Finite four-twist boundary for the manuscript weighted moment

This module closes the elementary reduction from the literal
genus-weighted selected-`L` sum to a finite reciprocal-polynomial moment of
the shape to which Wilson's quadratic-character estimate is meant to be
applied.

The reduction has three features which are important for source fidelity.

* The real part of the oddified selected `L`-value is nonnegative, and the
  selected value is at most twice that real part.  Thus no absolute value is
  needed around the finite reciprocal polynomial.
* Truncation at the exact natural endpoint `ceil(X)^2` is summed through the
  already proved norm error.  The complete genus-weighted error is at most
  `16`, rather than a termwise absolute polynomial moment.
* The finite polynomial sum is reindexed exactly into the four fixed
  modulus-eight twists `1`, `chi_4`, `chi_8`, and `chi_8'`, with the divisor
  weights and strict discriminant cutoffs from the manuscript.

The remaining analytic content is the explicitly named proposition
`Main4WilsonFinitePolynomialMoment`.  No theorem of Wilson, character-sum
estimate, or asymptotic bound is asserted in this file.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-! ## Positivity of the actual oddified selected value -/

/-- Exact real-part form of the Euler-factor identity at `2`. -/
theorem oddifiedKroneckerCharacter_LFunction_one_re_eq_eulerFactor_mul_selected
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    (DirichletCharacter.LFunction
      (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1).re =
      (1 -
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2).re / 2) *
        selectedKroneckerLValue D := by
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  have hid := congrArg Complex.re
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_LFunction_one
      D hD)
  have him :=
    kroneckerCharacterAtPositiveFundamentalDiscriminantC_apply_im D hD 2
  have hval : selectedKroneckerLValue D =
      (DirichletCharacter.LFunction
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1).re := by
    simp only [selectedKroneckerLValue, dif_pos hD]
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im, him,
    zero_div, sub_self, zero_mul, sub_zero] at hid
  rw [← hval] at hid
  exact hid

/-- The Euler factor introduced by oddification is at least `1/2`. -/
theorem one_half_le_oddifiedKroneckerCharacter_eulerFactor
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (1 : ℝ) / 2 ≤
      1 -
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2).re / 2 := by
  have hnorm :=
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD).norm_le_one 2
  have hre := Complex.re_le_norm
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2)
  nlinarith

/-- The actual oddified quadratic `L`-value has nonnegative real part. -/
theorem oddifiedKroneckerCharacter_LFunction_one_re_nonneg
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    0 ≤ (DirichletCharacter.LFunction
      (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1).re := by
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  rw [oddifiedKroneckerCharacter_LFunction_one_re_eq_eulerFactor_mul_selected]
  exact mul_nonneg
    (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (one_half_le_oddifiedKroneckerCharacter_eulerFactor D hD))
    (selectedKroneckerLValue_nonneg D)

/-- Removing the Euler factor at `2` costs at most the exact factor two,
without an absolute value around the oddified `L`-value. -/
theorem selectedKroneckerLValue_le_two_mul_re_oddifiedLFunction_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    selectedKroneckerLValue D ≤
      2 * (DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1).re := by
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  rw [oddifiedKroneckerCharacter_LFunction_one_re_eq_eulerFactor_mul_selected]
  have hfactor := one_half_le_oddifiedKroneckerCharacter_eulerFactor D hD
  have hL := selectedKroneckerLValue_nonneg D
  nlinarith

/-- Pointwise truncation inequality with the signed real polynomial kept
intact.  Only the difference between the analytic value and the polynomial
is measured by a norm. -/
theorem selectedKroneckerLValue_le_two_mul_oddJacobiPolynomial_add_error
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) (N : ℕ) :
    selectedKroneckerLValue D.val ≤
      2 * oddJacobiReciprocalPolynomial D.val N +
        2 * main4SelectedOddifiedTruncationError D N := by
  let _ : NeZero (2 * D.val) := ⟨by have := D.property.1; omega⟩
  let z : ℂ := DirichletCharacter.LFunction
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant
      D.val D.property) 1
  let p : ℝ := oddJacobiReciprocalPolynomial D.val N
  have hL : selectedKroneckerLValue D.val ≤ 2 * z.re :=
    selectedKroneckerLValue_le_two_mul_re_oddifiedLFunction_one
      D.val D.property
  have hre := Complex.re_le_norm (z - (p : ℂ))
  have hre' : z.re - p ≤ main4SelectedOddifiedTruncationError D N := by
    simpa only [z, p, Complex.sub_re, Complex.ofReal_re,
      main4SelectedOddifiedTruncationError] using hre
  dsimp only [p] at hre' ⊢
  nlinarith

/-! ## Exact real-cutoff and four-twist bookkeeping -/

/-- A strict cutoff by a real number agrees exactly with the strict cutoff
by its natural ceiling.  In particular, there is no endpoint loss when the
real cutoff is itself an integer. -/
theorem fundamentalDiscriminantsBelow_eq_natCeil (X : ℝ) :
    fundamentalDiscriminantsBelow X =
      fundamentalDiscriminantsBelow (⌈X⌉₊ : ℝ) := by
  ext D
  simp only [mem_fundamentalDiscriminantsBelow]
  constructor
  · rintro ⟨hD, hDX⟩
    exact ⟨hD, by exact_mod_cast (Nat.lt_ceil.mpr hDX)⟩
  · rintro ⟨hD, hDX⟩
    refine ⟨hD, Nat.lt_ceil.mp ?_⟩
    exact_mod_cast hDX

/-- The `D = 8m`, `m = 1 (mod 4)` radicand family.  It includes `m = 1`
when the strict cutoff contains the exceptional discriminant `D = 8`. -/
def main4EightOneBranchRadicandsBelow (X : ℝ) : Finset ℕ :=
  (main4EightBranchRadicandsBelow X).filter fun m ↦ m % 4 = 1

/-- The `D = 8m`, `m = 3 (mod 4)` radicand family. -/
def main4EightThreeBranchRadicandsBelow (X : ℝ) : Finset ℕ :=
  (main4EightBranchRadicandsBelow X).filter fun m ↦ m % 4 = 3

@[simp]
theorem mem_main4EightOneBranchRadicandsBelow {m : ℕ} {X : ℝ} :
    m ∈ main4EightOneBranchRadicandsBelow X ↔
      Odd m ∧ Squarefree m ∧ m % 4 = 1 ∧ ((8 * m : ℕ) : ℝ) < X := by
  simp only [main4EightOneBranchRadicandsBelow, Finset.mem_filter,
    mem_main4EightBranchRadicandsBelow]
  aesop

@[simp]
theorem mem_main4EightThreeBranchRadicandsBelow {m : ℕ} {X : ℝ} :
    m ∈ main4EightThreeBranchRadicandsBelow X ↔
      Odd m ∧ Squarefree m ∧ m % 4 = 3 ∧ ((8 * m : ℕ) : ℝ) < X := by
  simp only [main4EightThreeBranchRadicandsBelow, Finset.mem_filter,
    mem_main4EightBranchRadicandsBelow]
  aesop

/-- The signed genus-weighted odd-Jacobi polynomial before splitting into
the four fixed modulus-eight twists. -/
def main4SelectedOddJacobiWeightedPolynomialSum (X : ℝ) : ℝ :=
  ∑ D ∈ fundamentalDiscriminantsBelow X,
    genusWeight D * oddJacobiReciprocalPolynomial D (⌈X⌉₊ ^ 2)

/-- The exact finite four-twist reciprocal-polynomial sum at cutoff `X`.

The first two summands correspond to `D = m` and `D = 4m`.  The last two
split `D = 8m` by `m mod 4`.  The reciprocal divisor weights are exactly
`1 / tau(m)` and `1 / (2 tau(m))`, and every inner polynomial is truncated
at `ceil(X)^2`. -/
def main4WilsonFourTwistReciprocalPolynomialSum (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  (∑ m ∈ main4OddBranchRadicandsBelow X,
      (1 / (m.divisors.card : ℝ)) *
        main4TwistedJacobiReciprocalPolynomial 1 m N) +
  (∑ m ∈ main4FourBranchRadicandsBelow X,
      (1 / (2 * (m.divisors.card : ℝ))) *
        main4TwistedJacobiReciprocalPolynomial
          main4ChiFourModuloEight m N) +
  (∑ m ∈ main4EightOneBranchRadicandsBelow X,
      (1 / (2 * (m.divisors.card : ℝ))) *
        main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ m N) +
  ∑ m ∈ main4EightThreeBranchRadicandsBelow X,
      (1 / (2 * (m.divisors.card : ℝ))) *
        main4TwistedJacobiReciprocalPolynomial ZMod.χ₈' m N

/-- Exact reindexing of the selected odd-Jacobi polynomial into the four
fixed twists.  This includes the strict cutoffs, divisor weights, and the
`D = 8` exception. -/
theorem main4SelectedOddJacobiWeightedPolynomialSum_eq_fourTwists
    (X : ℝ) :
    main4SelectedOddJacobiWeightedPolynomialSum X =
      main4WilsonFourTwistReciprocalPolynomialSum X := by
  classical
  let N := ⌈X⌉₊ ^ 2
  unfold main4SelectedOddJacobiWeightedPolynomialSum
    main4WilsonFourTwistReciprocalPolynomialSum
  dsimp only
  rw [sum_genusWeight_mul_fundamentalDiscriminantsBelow_eq_main4_radical_sums
    (fun D ↦ oddJacobiReciprocalPolynomial D N) X]
  have hodd :
      (∑ m ∈ main4OddBranchRadicandsBelow X,
        (1 / (m.divisors.card : ℝ)) *
          oddJacobiReciprocalPolynomial m N) =
      ∑ m ∈ main4OddBranchRadicandsBelow X,
        (1 / (m.divisors.card : ℝ)) *
          main4TwistedJacobiReciprocalPolynomial 1 m N := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [oddJacobiReciprocalPolynomial_eq_main4TwistedOddBranch]
    exact (mem_main4OddBranchRadicandsBelow.mp hm).2.2.1
  have hfour :
      (∑ m ∈ main4FourBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) *
          oddJacobiReciprocalPolynomial (4 * m) N) =
      ∑ m ∈ main4FourBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) *
          main4TwistedJacobiReciprocalPolynomial
            main4ChiFourModuloEight m N := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [oddJacobiReciprocalPolynomial_eq_main4TwistedFourBranch]
    exact (mem_main4FourBranchRadicandsBelow.mp hm).2.2.1
  have hnotFilter :
      (main4EightBranchRadicandsBelow X).filter (fun m ↦ ¬m % 4 = 1) =
        main4EightThreeBranchRadicandsBelow X := by
    ext m
    simp only [Finset.mem_filter, main4EightThreeBranchRadicandsBelow]
    constructor
    · rintro ⟨hm, hnot⟩
      refine ⟨hm, ?_⟩
      obtain ⟨hodd, _, _⟩ := mem_main4EightBranchRadicandsBelow.mp hm
      rcases hodd with ⟨k, hk⟩
      omega
    · rintro ⟨hm, hthree⟩
      exact ⟨hm, by omega⟩
  have height :
      (∑ m ∈ main4EightBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) *
          oddJacobiReciprocalPolynomial (8 * m) N) =
      (∑ m ∈ main4EightOneBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) *
          main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ m N) +
      ∑ m ∈ main4EightThreeBranchRadicandsBelow X,
        (1 / (2 * (m.divisors.card : ℝ))) *
          main4TwistedJacobiReciprocalPolynomial ZMod.χ₈' m N := by
    let s := main4EightBranchRadicandsBelow X
    let F : ℕ → ℝ := fun m ↦
      (1 / (2 * (m.divisors.card : ℝ))) *
        oddJacobiReciprocalPolynomial (8 * m) N
    rw [← Finset.sum_filter_add_sum_filter_not s (fun m ↦ m % 4 = 1) F]
    change
      (∑ m ∈ main4EightOneBranchRadicandsBelow X, F m) +
        (∑ m ∈ s.filter (fun m ↦ ¬m % 4 = 1), F m) = _
    rw [hnotFilter]
    congr 1
    · apply Finset.sum_congr rfl
      intro m hm
      unfold F
      rw [oddJacobiReciprocalPolynomial_eq_main4TwistedEightOneBranch]
      exact (Finset.mem_filter.mp hm).2
    · apply Finset.sum_congr rfl
      intro m hm
      unfold F
      rw [oddJacobiReciprocalPolynomial_eq_main4TwistedEightThreeBranch]
      exact (Finset.mem_filter.mp hm).2
  rw [hodd, hfour, height]
  dsimp only [N]
  ring

/-! ## Summed truncation and the explicit analytic boundary -/

/-- The aggregate truncation error at a real cutoff, using the exact common
endpoint `ceil(X)^2`. -/
def main4SelectedOddifiedTruncationErrorSumAtRealCutoff (X : ℝ) : ℝ := by
  classical
  exact
    ∑ D ∈ (fundamentalDiscriminantsBelow X).subtype
        PositiveFundamentalDiscriminant,
      genusWeight D.val *
        main4SelectedOddifiedTruncationError D (⌈X⌉₊ ^ 2)

/-- The real-cutoff error is definitionally the proved natural-cutoff error
after the exact ceiling transport. -/
theorem main4SelectedOddifiedTruncationErrorSumAtRealCutoff_eq_natCeil
    (X : ℝ) :
    main4SelectedOddifiedTruncationErrorSumAtRealCutoff X =
      main4SelectedOddifiedTruncationErrorSum ⌈X⌉₊ := by
  classical
  unfold main4SelectedOddifiedTruncationErrorSumAtRealCutoff
    main4SelectedOddifiedTruncationErrorSum
  rw [fundamentalDiscriminantsBelow_eq_natCeil]

/-- The complete real-cutoff truncation error is at most `16`. -/
theorem main4SelectedOddifiedTruncationErrorSumAtRealCutoff_le_sixteen
    {X : ℝ} (hX : 0 < X) :
    main4SelectedOddifiedTruncationErrorSumAtRealCutoff X ≤ 16 := by
  rw [main4SelectedOddifiedTruncationErrorSumAtRealCutoff_eq_natCeil]
  exact main4SelectedOddifiedTruncationErrorSum_le_sixteen ⌈X⌉₊
    (Nat.ceil_pos.mpr hX)

/-- Summing the pointwise signed-polynomial inequality introduces only the
aggregate norm error.  There is no sum of absolute polynomial values. -/
theorem main4OddClassWeightedFirstMomentSum_le_polynomial_add_error
    (X : ℝ) :
    main4OddClassWeightedFirstMomentSum X ≤
      2 * main4SelectedOddJacobiWeightedPolynomialSum X +
        2 * main4SelectedOddifiedTruncationErrorSumAtRealCutoff X := by
  classical
  unfold main4OddClassWeightedFirstMomentSum
    main4SelectedOddJacobiWeightedPolynomialSum
    main4SelectedOddifiedTruncationErrorSumAtRealCutoff
  rw [← Finset.sum_subtype_of_mem
    (fun D : ℕ ↦ genusWeight D * selectedKroneckerLValue D)
    (fun D hD ↦ (mem_fundamentalDiscriminantsBelow.mp hD).1)]
  rw [← Finset.sum_subtype_of_mem
    (fun D : ℕ ↦ genusWeight D *
      oddJacobiReciprocalPolynomial D (⌈X⌉₊ ^ 2))
    (fun D hD ↦ (mem_fundamentalDiscriminantsBelow.mp hD).1)]
  let s := (fundamentalDiscriminantsBelow X).subtype
    PositiveFundamentalDiscriminant
  change (∑ D ∈ s,
    genusWeight D.val * selectedKroneckerLValue D.val) ≤ _
  calc
    (∑ D ∈ s, genusWeight D.val * selectedKroneckerLValue D.val) ≤
        ∑ D ∈ s, genusWeight D.val *
          (2 * oddJacobiReciprocalPolynomial D.val (⌈X⌉₊ ^ 2) +
            2 * main4SelectedOddifiedTruncationError D (⌈X⌉₊ ^ 2)) := by
      apply Finset.sum_le_sum
      intro D _hD
      exact mul_le_mul_of_nonneg_left
        (selectedKroneckerLValue_le_two_mul_oddJacobiPolynomial_add_error
          D (⌈X⌉₊ ^ 2))
        (genusWeight_nonneg D.val)
    _ = ∑ D ∈ s,
          (2 * (genusWeight D.val *
              oddJacobiReciprocalPolynomial D.val (⌈X⌉₊ ^ 2)) +
            2 * (genusWeight D.val *
              main4SelectedOddifiedTruncationError D (⌈X⌉₊ ^ 2))) := by
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = 2 * (∑ D ∈ s, genusWeight D.val *
          oddJacobiReciprocalPolynomial D.val (⌈X⌉₊ ^ 2)) +
        2 * (∑ D ∈ s, genusWeight D.val *
          main4SelectedOddifiedTruncationError D (⌈X⌉₊ ^ 2)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Finite four-twist form of the reduction, with the aggregate error
already replaced by its uniform constant. -/
theorem main4OddClassWeightedFirstMomentSum_le_two_mul_fourTwists_add_thirtyTwo
    {X : ℝ} (hX : 0 < X) :
    main4OddClassWeightedFirstMomentSum X ≤
      2 * main4WilsonFourTwistReciprocalPolynomialSum X + 32 := by
  have hbase := main4OddClassWeightedFirstMomentSum_le_polynomial_add_error X
  rw [main4SelectedOddJacobiWeightedPolynomialSum_eq_fourTwists] at hbase
  have herr :=
    main4SelectedOddifiedTruncationErrorSumAtRealCutoff_le_sixteen hX
  nlinarith

/-- The main4 scale is at least one in the eventual range. -/
theorem one_le_main4WeightedFirstMomentScale {X : ℝ} (hX : 3 ≤ X) :
    1 ≤ X / Real.sqrt (Real.log X) := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogle : Real.log X ≤ X := by
    have h := Real.log_le_sub_one_of_pos hXpos
    linarith
  have hXsq : X ≤ X ^ 2 := by nlinarith
  have hsqrtle : Real.sqrt (Real.log X) ≤ X := by
    rw [Real.sqrt_le_iff]
    exact ⟨hXpos.le, hlogle.trans hXsq⟩
  exact (le_div_iff₀ (Real.sqrt_pos.2 hlog)).2 (by simpa using hsqrtle)

/-- The exact finite analytic interface left for Wilson's estimate.

One positive constant is chosen before the real cutoff.  The summand,
divisor weights, four fixed twists, strict branch cutoffs, and truncation
endpoint are all concrete finite objects defined above. -/
def Main4WilsonFinitePolynomialMoment : Prop :=
  ∃ Cwilson : ℝ, 0 < Cwilson ∧
    ∀ᶠ X : ℝ in atTop,
      main4WilsonFourTwistReciprocalPolynomialSum X ≤
        Cwilson * (X / Real.sqrt (Real.log X))

/-- The finite Wilson-shaped polynomial moment implies the exact weighted
first moment used by the manuscript completion. -/
theorem main4OddClassWeightedFirstMoment_of_wilsonFinitePolynomialMoment
    (hWilson : Main4WilsonFinitePolynomialMoment) :
    Main4OddClassWeightedFirstMoment := by
  obtain ⟨Cwilson, hCwilson, hWilsonBound⟩ := hWilson
  refine ⟨2 * Cwilson + 32, by positivity, ?_⟩
  filter_upwards [hWilsonBound, eventually_ge_atTop (3 : ℝ)] with
      X hPolynomial hX
  have hselected :=
    main4OddClassWeightedFirstMomentSum_le_two_mul_fourTwists_add_thirtyTwo
      (show 0 < X by linarith)
  have hscale := one_le_main4WeightedFirstMomentScale hX
  calc
    main4OddClassWeightedFirstMomentSum X ≤
        2 * main4WilsonFourTwistReciprocalPolynomialSum X + 32 := hselected
    _ ≤ 2 * (Cwilson * (X / Real.sqrt (Real.log X))) + 32 := by
      nlinarith
    _ ≤ (2 * Cwilson + 32) *
        (X / Real.sqrt (Real.log X)) := by
      nlinarith

/-- Corollary 1.2, conditional on exactly the finite four-twist analytic
moment left above. -/
theorem realQuadraticFieldOddClassAverageAssertion_conditional_on_wilsonFinitePolynomialMoment
    (hWilson : Main4WilsonFinitePolynomialMoment) :
    RealQuadraticFieldOddClassAverageAssertion := by
  exact
    realQuadraticFieldOddClassAverageAssertion_conditional_on_main4WeightedFirstMoment
      (main4OddClassWeightedFirstMoment_of_wilsonFinitePolynomialMoment hWilson)

end

end PellPaper
