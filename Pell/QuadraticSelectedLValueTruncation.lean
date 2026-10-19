import Pell.OddJacobiReciprocalPolynomial
import Pell.NonprincipalDirichletLValueTruncation
import Pell.QuadraticKroneckerCharacterOddification

/-!
# The actual selected L-value controlled by a finite odd Jacobi polynomial

The actual oddified selected character has precisely the finite real
polynomial defined here as its reciprocal prefix. The proved all-nonprincipal
L-value truncation and the selected odd Euler-factor bound give a pointwise
square estimate with explicit constants. No sign assumption on the finite
polynomial and no caller-supplied analytic bound are used.
-/

namespace PellPaper

open scoped BigOperators

/-- The reciprocal prefix of the actual oddified selected character is the
complex image of the literal real odd Jacobi polynomial. -/
theorem oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial
    (D N : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (∑ n ∈ Finset.Icc 1 N,
      oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD
        (n : ZMod (2 * D)) / (n : ℂ)) =
      (oddJacobiReciprocalPolynomial D N : ℂ) := by
  rw [oddJacobiReciprocalPolynomial, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  rw [oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_natCast]
  by_cases hn : Odd n <;> simp [hn]

/-- Approximation of the actual oddified analytic L-value by the finite
polynomial, at the exact natural cutoff `N > 0`. -/
theorem norm_oddifiedKroneckerCharacter_LFunction_one_sub_polynomial_le
    (D N : ℕ) (hD : PositiveFundamentalDiscriminant D) (hN : 0 < N) :
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    ‖DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1 -
        (oddJacobiReciprocalPolynomial D N : ℂ)‖ ≤
      4 * Real.sqrt (2 * (D : ℝ)) * (1 + Real.log (2 * (D : ℝ))) / (N : ℝ) := by
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  have h := norm_nonprincipalDirichletCharacter_LFunction_one_sub_prefix_le
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD)
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_ne_one D hD) N hN
  rw [oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial D N hD] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- The square of the actual selected L-value is bounded by the finite odd
Jacobi polynomial square and an explicit truncation error. -/
theorem selectedKroneckerLValue_sq_le_oddJacobiReciprocalPolynomial
    (D N : ℕ) (hD : PositiveFundamentalDiscriminant D) (hN : 0 < N) :
    (selectedKroneckerLValue D) ^ 2 ≤
      8 * (oddJacobiReciprocalPolynomial D N) ^ 2 +
        256 * (D : ℝ) * (1 + Real.log (2 * (D : ℝ))) ^ 2 / (N : ℝ) ^ 2 := by
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  let z : ℂ := DirichletCharacter.LFunction
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1
  let p : ℝ := oddJacobiReciprocalPolynomial D N
  let δ : ℝ :=
    4 * Real.sqrt (2 * (D : ℝ)) * (1 + Real.log (2 * (D : ℝ))) / (N : ℝ)
  have hnorm : ‖z - (p : ℂ)‖ ≤ δ :=
    norm_oddifiedKroneckerCharacter_LFunction_one_sub_polynomial_le D N hD hN
  have herr : |z.re - p| ≤ δ := by
    have hre := Complex.abs_re_le_norm (z - (p : ℂ))
    have hre' : |z.re - p| ≤ ‖z - (p : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using hre
    exact hre'.trans hnorm
  have hL : selectedKroneckerLValue D ≤ 2 * |z.re| :=
    selectedKroneckerLValue_le_two_mul_abs_re_oddifiedLFunction_one D hD
  have hLpos : 0 ≤ selectedKroneckerLValue D := (selectedKroneckerLValue_pos D hD).le
  have hsqL : (selectedKroneckerLValue D) ^ 2 ≤ 4 * z.re ^ 2 := by
    nlinarith [mul_self_le_mul_self hLpos hL, sq_abs z.re]
  have hsqerr : (z.re - p) ^ 2 ≤ δ ^ 2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg (z.re - p)) herr, sq_abs (z.re - p)]
  have hsq : (selectedKroneckerLValue D) ^ 2 ≤ 8 * p ^ 2 + 8 * δ ^ 2 := by
    nlinarith [sq_nonneg (z.re - 2 * p)]
  have hsqrt : Real.sqrt (2 * (D : ℝ)) ^ 2 = 2 * (D : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    (selectedKroneckerLValue D) ^ 2 ≤ 8 * p ^ 2 + 8 * δ ^ 2 := hsq
    _ = 8 * (oddJacobiReciprocalPolynomial D N) ^ 2 +
        256 * (D : ℝ) * (1 + Real.log (2 * (D : ℝ))) ^ 2 / (N : ℝ) ^ 2 := by
      dsimp only [p, δ]
      simp only [div_pow, mul_pow, hsqrt]
      ring

end PellPaper
