import Pell.CorollaryOddPartGenusAlgebra
import Pell.QuadraticSelectedLValueTruncation

/-!
# Source-shaped L-value truncation for the manuscript moment

The weighted first-moment argument in the manuscript truncates each selected
nonprincipal quadratic character at the square of the outer cutoff and uses
an error of size `O(m / Y^2)` in each of the `m`, `4m`, and `8m` branches.

The project already proves a stronger all-nonprincipal Pólya--Vinogradov
truncation.  This module turns that estimate into the source-shaped linear
modulus bound, specializes it to the actual oddified quadratic character,
and proves that the complete genus-weighted truncation error over
`D < Y` is at most the absolute constant `16`.

No character-sum or moment estimate is assumed here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The logarithmic Pólya--Vinogradov scale is at most twice the level.
This elementary weakening is what recovers the paper's periodicity-shaped
`O(q / N)` truncation error from the stronger proved estimate. -/
theorem sqrt_mul_one_add_log_le_two_mul_self
    {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * (1 + Real.log x) ≤ 2 * x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrtSq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hsqrt1 : 1 ≤ Real.sqrt x := by
    nlinarith
  have hlogSqrt := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hsqrt1)
  have hlog : Real.log x ≤ 2 * (Real.sqrt x - 1) := by
    rw [Real.log_sqrt hx0] at hlogSqrt
    linarith
  have honeLog : 1 + Real.log x ≤ 2 * Real.sqrt x := by
    linarith
  calc
    Real.sqrt x * (1 + Real.log x) ≤
        Real.sqrt x * (2 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left honeLog hsqrt0
    _ = 2 * x := by nlinarith

/-- Every nonprincipal character has the source-shaped truncation error
`8q/N`.  This is valid for imprimitive characters and concerns the actual
analytic `LFunction` at one. -/
theorem norm_nonprincipalDirichletCharacter_LFunction_one_sub_prefix_le_level
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (N : ℕ) (hN : 0 < N) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q) / (n : ℂ)‖ ≤
      8 * (q : ℝ) / (N : ℝ) := by
  have hqNat : 1 ≤ q := (NeZero.pos q)
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hqNat
  have hscale := sqrt_mul_one_add_log_le_two_mul_self hqReal
  have hbase := norm_nonprincipalDirichletCharacter_LFunction_one_sub_prefix_le
    chi hchi N hN
  calc
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q) / (n : ℂ)‖ ≤
        4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) / (N : ℝ) := hbase
    _ ≤ 8 * (q : ℝ) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [hscale]

/-- The actual oddified quadratic character at a positive fundamental
discriminant has truncation error at most `16D/N`.  Its reciprocal prefix is
the literal finite odd Jacobi polynomial used by the project. -/
theorem norm_oddifiedKroneckerCharacter_LFunction_one_sub_polynomial_le_level
    (D N : ℕ) (hD : PositiveFundamentalDiscriminant D) (hN : 0 < N) :
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    ‖DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1 -
        (oddJacobiReciprocalPolynomial D N : ℂ)‖ ≤
      16 * (D : ℝ) / (N : ℝ) := by
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  have h :=
    norm_nonprincipalDirichletCharacter_LFunction_one_sub_prefix_le_level
      (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD)
      (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_ne_one D hD)
      N hN
  rw [oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial D N hD] at h
  calc
    ‖DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1 -
        (oddJacobiReciprocalPolynomial D N : ℂ)‖ ≤
        8 * ((2 * D : ℕ) : ℝ) / (N : ℝ) := h
    _ = 16 * (D : ℝ) / (N : ℝ) := by
      norm_num [Nat.cast_mul]
      ring

/-- The nonnegative truncation error for one actual selected discriminant. -/
def main4SelectedOddifiedTruncationError
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) (N : ℕ) : ℝ :=
  let _ : NeZero (2 * D.val) := ⟨by have := D.property.1; omega⟩
  ‖DirichletCharacter.LFunction
      (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant
        D.val D.property) 1 -
      (oddJacobiReciprocalPolynomial D.val N : ℂ)‖

theorem main4SelectedOddifiedTruncationError_nonneg
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) (N : ℕ) :
    0 ≤ main4SelectedOddifiedTruncationError D N := by
  unfold main4SelectedOddifiedTruncationError
  exact norm_nonneg _

theorem main4SelectedOddifiedTruncationError_le
    (D : {D : ℕ // PositiveFundamentalDiscriminant D})
    (N : ℕ) (hN : 0 < N) :
    main4SelectedOddifiedTruncationError D N ≤
      16 * (D.val : ℝ) / (N : ℝ) := by
  unfold main4SelectedOddifiedTruncationError
  exact norm_oddifiedKroneckerCharacter_LFunction_one_sub_polynomial_le_level
    D.val N D.property hN

/-- The full genus-weighted error made by truncating every oddified selected
quadratic character's `L`-value with `D < Y` at the exact natural endpoint
`Y^2`. -/
def main4SelectedOddifiedTruncationErrorSum (Y : ℕ) : ℝ := by
  classical
  exact
    ∑ D ∈ (fundamentalDiscriminantsBelow (Y : ℝ)).subtype
        PositiveFundamentalDiscriminant,
      genusWeight D.val * main4SelectedOddifiedTruncationError D (Y ^ 2)

/-- The aggregate source truncation error is uniformly `O(1)`, with the
explicit absolute constant `16`.  The constant is independent of `Y`; the
strict cutoff is exactly the project's convention `D < Y`. -/
theorem main4SelectedOddifiedTruncationErrorSum_le_sixteen
    (Y : ℕ) (hY : 0 < Y) :
    main4SelectedOddifiedTruncationErrorSum Y ≤ 16 := by
  classical
  let s := (fundamentalDiscriminantsBelow (Y : ℝ)).subtype
    PositiveFundamentalDiscriminant
  have hYReal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hYsq : 0 < Y ^ 2 := pow_pos hY 2
  have hcard : s.card ≤ Y := by
    dsimp only [s]
    rw [Finset.card_subtype]
    calc
      ((fundamentalDiscriminantsBelow (Y : ℝ)).filter
          PositiveFundamentalDiscriminant).card ≤
          (fundamentalDiscriminantsBelow (Y : ℝ)).card :=
        Finset.card_filter_le _ _
      _ ≤ (Finset.range Y).card := by
        apply Finset.card_le_card
        intro D hDmem
        rw [Finset.mem_range]
        have hDY := (mem_fundamentalDiscriminantsBelow.mp hDmem).2
        exact_mod_cast hDY
      _ = Y := Finset.card_range Y
  have hpoint : ∀ D ∈ s,
      genusWeight D.val *
          main4SelectedOddifiedTruncationError D (Y ^ 2) ≤
        16 / (Y : ℝ) := by
    intro D hDmem
    have hDbase : D.val ∈ fundamentalDiscriminantsBelow (Y : ℝ) := by
      simpa only [s, Finset.mem_subtype] using hDmem
    have hDY : (D.val : ℝ) < Y :=
      (mem_fundamentalDiscriminantsBelow.mp hDbase).2
    calc
      genusWeight D.val *
          main4SelectedOddifiedTruncationError D (Y ^ 2) ≤
          main4SelectedOddifiedTruncationError D (Y ^ 2) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (genusWeight_le_one D.val)
            (main4SelectedOddifiedTruncationError_nonneg D (Y ^ 2))
      _ ≤ 16 * (D.val : ℝ) / ((Y ^ 2 : ℕ) : ℝ) :=
        main4SelectedOddifiedTruncationError_le D (Y ^ 2) hYsq
      _ ≤ 16 * (Y : ℝ) / ((Y ^ 2 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hDY.le (by norm_num)
      _ = 16 / (Y : ℝ) := by
        norm_num [Nat.cast_pow]
        field_simp
  unfold main4SelectedOddifiedTruncationErrorSum
  change (∑ D ∈ s,
      genusWeight D.val *
        main4SelectedOddifiedTruncationError D (Y ^ 2)) ≤ 16
  calc
    (∑ D ∈ s,
        genusWeight D.val *
          main4SelectedOddifiedTruncationError D (Y ^ 2)) ≤
        ∑ _D ∈ s, 16 / (Y : ℝ) := by
      exact Finset.sum_le_sum fun D hDmem ↦ hpoint D hDmem
    _ = (s.card : ℝ) * (16 / (Y : ℝ)) := by simp
    _ ≤ (Y : ℝ) * (16 / (Y : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      positivity
    _ = 16 := by field_simp

end

end PellPaper
