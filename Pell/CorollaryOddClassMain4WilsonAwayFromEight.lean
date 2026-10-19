import Pell.CorollaryOddClassMain4FiniteWilsonReduction

/-!
# Removing the exceptional `D = 8` term from the finite Wilson boundary

Wilson's source family is naturally stated for nontrivial odd squarefree
radicands `1 < m`.  In the first `D = 8m` branch, the exact discriminant
decomposition used by the manuscript also contains `m = 1`, namely `D = 8`.

This module removes that one term from the analytic interface and bounds it
elementarily.  The bound comes from the already proved truncation estimate
for the actual oddified `D = 8` character.  The strict cutoff remains
`D < X`, and every finite reciprocal polynomial remains truncated at the
exact endpoint `ceil(X)^2`.

The only remaining analytic content is the explicitly named proposition
`Main4WilsonFinitePolynomialMomentAwayFromEight`.  No estimate of Wilson is
asserted here.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-! ## The source-shaped away-from-eight sum -/

/-- The `chi_8` radicands after removing the sole exceptional value `m = 1`.
All original oddness, squarefreeness, congruence, and strict-cutoff
conditions are retained. -/
def main4EightOneBranchRadicandsBelowAwayFromEight (X : ℝ) : Finset ℕ :=
  (main4EightOneBranchRadicandsBelow X).filter (1 < ·)

@[simp]
theorem mem_main4EightOneBranchRadicandsBelowAwayFromEight
    {m : ℕ} {X : ℝ} :
    m ∈ main4EightOneBranchRadicandsBelowAwayFromEight X ↔
      1 < m ∧ Odd m ∧ Squarefree m ∧ m % 4 = 1 ∧
        ((8 * m : ℕ) : ℝ) < X := by
  simp only [main4EightOneBranchRadicandsBelowAwayFromEight,
    Finset.mem_filter, mem_main4EightOneBranchRadicandsBelow]
  aesop

/-- The away-from-eight `chi_8` family is exactly the congruence-one part
of the common nontrivial odd-squarefree Wilson family at cutoff `X / 8`. -/
theorem main4EightOneBranchRadicandsBelowAwayFromEight_eq_nontrivial_filter
    (X : ℝ) :
    main4EightOneBranchRadicandsBelowAwayFromEight X =
      (main4NontrivialOddSquarefreeRadicandsBelow (X / 8)).filter
        fun m ↦ m % 4 = 1 := by
  ext m
  simp only [mem_main4EightOneBranchRadicandsBelowAwayFromEight,
    Finset.mem_filter, mem_main4NontrivialOddSquarefreeRadicandsBelow]
  constructor
  · rintro ⟨hm, hodd, hsf, hmod, hmX⟩
    exact ⟨⟨hm, hodd, hsf, by norm_num at hmX ⊢; linarith⟩, hmod⟩
  · rintro ⟨⟨hm, hodd, hsf, hmX⟩, hmod⟩
    exact ⟨hm, hodd, hsf, hmod, by norm_num at hmX ⊢; linarith⟩

/-- The finite four-twist reciprocal-polynomial sum with the `chi_8`
branch restricted to `1 < m`.  The other three branches, their weights,
their strict discriminant cutoffs, and the common endpoint `ceil(X)^2` are
unchanged. -/
def main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight
    (X : ℝ) : ℝ :=
  let N := ⌈X⌉₊ ^ 2
  (∑ m ∈ main4OddBranchRadicandsBelow X,
      (1 / (m.divisors.card : ℝ)) *
        main4TwistedJacobiReciprocalPolynomial 1 m N) +
  (∑ m ∈ main4FourBranchRadicandsBelow X,
      (1 / (2 * (m.divisors.card : ℝ))) *
        main4TwistedJacobiReciprocalPolynomial
          main4ChiFourModuloEight m N) +
  (∑ m ∈ main4EightOneBranchRadicandsBelowAwayFromEight X,
      (1 / (2 * (m.divisors.card : ℝ))) *
        main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ m N) +
  ∑ m ∈ main4EightThreeBranchRadicandsBelow X,
      (1 / (2 * (m.divisors.card : ℝ))) *
        main4TwistedJacobiReciprocalPolynomial ZMod.χ₈' m N

/-- The `D = 8` contribution to the full finite four-twist sum.  It is
present precisely when the strict cutoff satisfies `8 < X`. -/
def main4ExceptionalEightFinitePolynomialContribution (X : ℝ) : ℝ :=
  if (8 : ℝ) < X then
    (1 / 2 : ℝ) *
      main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ 1 (⌈X⌉₊ ^ 2)
  else 0

/-- Inside the congruence-one `8m` branch, the complement of `1 < m` is
exactly the conditional singleton `m = 1`. -/
theorem main4EightOneBranchRadicandsBelow_filter_not_one_lt
    (X : ℝ) :
    (main4EightOneBranchRadicandsBelow X).filter (fun m ↦ ¬1 < m) =
      if (8 : ℝ) < X then {1} else ∅ := by
  by_cases hX : (8 : ℝ) < X
  · rw [if_pos hX]
    ext m
    simp only [Finset.mem_filter,
      mem_main4EightOneBranchRadicandsBelow, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hodd, _hsf, _hmod, hmX⟩, hm⟩
      rcases hodd with ⟨k, hk⟩
      omega
    · rintro rfl
      exact ⟨⟨by norm_num, by norm_num, by norm_num,
        by norm_num at hX ⊢; exact hX⟩, by norm_num⟩
  · rw [if_neg hX]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmBranch, hm⟩ := hm
    obtain ⟨hodd, _hsf, _hmod, hmX⟩ :=
      mem_main4EightOneBranchRadicandsBelow.mp hmBranch
    have hmOne : m = 1 := by
      rcases hodd with ⟨k, hk⟩
      omega
    subst m
    exact hX (by norm_num at hmX ⊢; exact hmX)

/-- Exact separation of the exceptional discriminant from the full
four-twist polynomial sum. -/
theorem main4WilsonFourTwistReciprocalPolynomialSum_eq_awayFromEight_add_exception
    (X : ℝ) :
    main4WilsonFourTwistReciprocalPolynomialSum X =
      main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X +
        main4ExceptionalEightFinitePolynomialContribution X := by
  classical
  let N := ⌈X⌉₊ ^ 2
  let F : ℕ → ℝ := fun m ↦
    (1 / (2 * (m.divisors.card : ℝ))) *
      main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ m N
  have hsplit :
      (∑ m ∈ main4EightOneBranchRadicandsBelow X, F m) =
        (∑ m ∈ main4EightOneBranchRadicandsBelowAwayFromEight X, F m) +
          (if (8 : ℝ) < X then F 1 else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (main4EightOneBranchRadicandsBelow X) (1 < ·) F]
    rw [main4EightOneBranchRadicandsBelow_filter_not_one_lt]
    unfold main4EightOneBranchRadicandsBelowAwayFromEight
    by_cases hX : (8 : ℝ) < X <;> simp [hX]
  have hFone : F 1 =
      (1 / 2 : ℝ) *
        main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ 1 (⌈X⌉₊ ^ 2) := by
    dsimp only [F, N]
    rw [Nat.divisors_one]
    norm_num
  unfold main4WilsonFourTwistReciprocalPolynomialSum
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight
    main4ExceptionalEightFinitePolynomialContribution
  dsimp only
  change _ + _ + (∑ m ∈ main4EightOneBranchRadicandsBelow X, F m) + _ = _
  rw [hsplit]
  by_cases hX : (8 : ℝ) < X
  · simp only [if_pos hX, hFone]
    ring
  · simp only [if_neg hX]
    ring

/-! ## Uniform elementary control of `D = 8` -/

/-- A fixed nonnegative constant controlling every finite `D = 8`
reciprocal polynomial.  The numerical value is irrelevant to the eventual
moment; the `128` is the proved `16D/N` truncation constant at `D = 8` and
`N ≥ 1`. -/
def main4ExceptionalEightFinitePolynomialBound : ℝ := by
  let hD : PositiveFundamentalDiscriminant 8 :=
    positiveFundamentalDiscriminant_iff_main4_decomposition.mpr
      (Or.inr (Or.inr ⟨1, by norm_num, by norm_num, by norm_num⟩))
  let _ : NeZero (2 * 8) := ⟨by norm_num⟩
  exact
    ‖DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant 8 hD) 1‖ +
      128

theorem main4ExceptionalEightFinitePolynomialBound_nonneg :
    0 ≤ main4ExceptionalEightFinitePolynomialBound := by
  unfold main4ExceptionalEightFinitePolynomialBound
  positivity

/-- Every positive-length `chi_8`, `m = 1` reciprocal polynomial is bounded
above by the fixed exceptional constant. -/
theorem main4TwistedJacobiReciprocalPolynomial_chiEight_one_le_bound
    (N : ℕ) (hN : 0 < N) :
    main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ 1 N ≤
      main4ExceptionalEightFinitePolynomialBound := by
  let hD : PositiveFundamentalDiscriminant 8 :=
    positiveFundamentalDiscriminant_iff_main4_decomposition.mpr
      (Or.inr (Or.inr ⟨1, by norm_num, by norm_num, by norm_num⟩))
  let _ : NeZero (2 * 8) := ⟨by norm_num⟩
  let z : ℂ := DirichletCharacter.LFunction
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant 8 hD) 1
  let p : ℝ := main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ 1 N
  have herr :=
    norm_oddifiedKroneckerCharacter_LFunction_one_sub_polynomial_le_level
      8 N hD hN
  rw [oddJacobiReciprocalPolynomial_eq_main4TwistedEightOneBranch
    1 N (by norm_num)] at herr
  norm_num at herr
  have htriangle : ‖(p : ℂ)‖ ≤ ‖z‖ + ‖z - (p : ℂ)‖ := by
    calc
      ‖(p : ℂ)‖ = ‖z - (z - (p : ℂ))‖ := by ring_nf
      _ ≤ ‖z‖ + ‖z - (p : ℂ)‖ := norm_sub_le z (z - (p : ℂ))
  have hpNorm : p ≤ ‖(p : ℂ)‖ := by
    simpa only [Complex.ofReal_re] using Complex.re_le_norm (p : ℂ)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have herror : 128 / (N : ℝ) ≤ 128 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  unfold main4ExceptionalEightFinitePolynomialBound
  dsimp only
  change p ≤ ‖z‖ + 128
  calc
    p ≤ ‖(p : ℂ)‖ := hpNorm
    _ ≤ ‖z‖ + ‖z - (p : ℂ)‖ := htriangle
    _ ≤ ‖z‖ + (128 / (N : ℝ)) := by
      exact add_le_add_right (by simpa only [z, p] using herr) _
    _ ≤ ‖z‖ + 128 := add_le_add_right herror _

/-- The conditional `D = 8` summand of the full four-twist moment is
uniformly bounded, with no assumption on `X`. -/
theorem main4ExceptionalEightFinitePolynomialContribution_le_bound
    (X : ℝ) :
    main4ExceptionalEightFinitePolynomialContribution X ≤
      main4ExceptionalEightFinitePolynomialBound := by
  by_cases hX : (8 : ℝ) < X
  · rw [main4ExceptionalEightFinitePolynomialContribution, if_pos hX]
    have hceil : 0 < ⌈X⌉₊ := Nat.ceil_pos.mpr (by linarith)
    have hpoly :=
      main4TwistedJacobiReciprocalPolynomial_chiEight_one_le_bound
        (⌈X⌉₊ ^ 2) (pow_pos hceil 2)
    have hbound := main4ExceptionalEightFinitePolynomialBound_nonneg
    nlinarith
  · rw [main4ExceptionalEightFinitePolynomialContribution, if_neg hX]
    exact main4ExceptionalEightFinitePolynomialBound_nonneg

/-! ## The away-from-eight analytic interface and capstones -/

/-- The source-shaped finite analytic interface: one positive constant is
chosen before the real cutoff, and Wilson's four-twist polynomial sum is
restricted to nontrivial radicands in its `chi_8` branch. -/
def Main4WilsonFinitePolynomialMomentAwayFromEight : Prop :=
  ∃ Cwilson : ℝ, 0 < Cwilson ∧
    ∀ᶠ X : ℝ in atTop,
      main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X ≤
        Cwilson * (X / Real.sqrt (Real.log X))

/-- An away-from-eight Wilson moment implies the original finite moment;
the exceptional `D = 8` term is absorbed into the eventual scale by its
fixed elementary bound. -/
theorem main4WilsonFinitePolynomialMoment_of_awayFromEight
    (hWilson : Main4WilsonFinitePolynomialMomentAwayFromEight) :
    Main4WilsonFinitePolynomialMoment := by
  obtain ⟨Cwilson, hCwilson, hWilsonBound⟩ := hWilson
  let B := main4ExceptionalEightFinitePolynomialBound
  have hB : 0 ≤ B := main4ExceptionalEightFinitePolynomialBound_nonneg
  refine ⟨Cwilson + B, add_pos_of_pos_of_nonneg hCwilson hB, ?_⟩
  filter_upwards [hWilsonBound, eventually_ge_atTop (3 : ℝ)] with
      X hAway hX
  have hscale := one_le_main4WeightedFirstMomentScale hX
  have hException :=
    main4ExceptionalEightFinitePolynomialContribution_le_bound X
  rw [main4WilsonFourTwistReciprocalPolynomialSum_eq_awayFromEight_add_exception]
  change _ ≤ (Cwilson + B) * (X / Real.sqrt (Real.log X))
  calc
    main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X +
        main4ExceptionalEightFinitePolynomialContribution X ≤
        main4WilsonFourTwistReciprocalPolynomialSumAwayFromEight X + B :=
      add_le_add_right hException _
    _ ≤ Cwilson * (X / Real.sqrt (Real.log X)) + B :=
      add_le_add_left hAway _
    _ ≤ (Cwilson + B) * (X / Real.sqrt (Real.log X)) := by
      nlinarith

/-- The source-shaped away-from-eight finite moment implies the exact
weighted first moment used in the manuscript completion. -/
theorem main4OddClassWeightedFirstMoment_of_wilsonFinitePolynomialMomentAwayFromEight
    (hWilson : Main4WilsonFinitePolynomialMomentAwayFromEight) :
    Main4OddClassWeightedFirstMoment :=
  main4OddClassWeightedFirstMoment_of_wilsonFinitePolynomialMoment
    (main4WilsonFinitePolynomialMoment_of_awayFromEight hWilson)

/-- Corollary 1.2, conditional only on the away-from-eight finite Wilson
moment above. -/
theorem realQuadraticFieldOddClassAverageAssertion_conditional_on_wilsonFinitePolynomialMomentAwayFromEight
    (hWilson : Main4WilsonFinitePolynomialMomentAwayFromEight) :
    RealQuadraticFieldOddClassAverageAssertion :=
  realQuadraticFieldOddClassAverageAssertion_conditional_on_wilsonFinitePolynomialMoment
    (main4WilsonFinitePolynomialMoment_of_awayFromEight hWilson)

end

end PellPaper
