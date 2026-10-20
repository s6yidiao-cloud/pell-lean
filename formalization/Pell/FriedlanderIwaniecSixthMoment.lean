import Pell.FriedlanderIwaniecCharacterMoment
import Pell.FriedlanderIwaniecCubicAggregate
import Pell.FriedlanderIwaniecHolderReduction
import Mathlib.Data.Real.Sign

/-!
# The assembled sixth-moment inequality of Friedlander--Iwaniec

This module joins the finite Hölder reduction, the cubic product-fibre
regrouping, Cauchy's inequality, the `tauThree` aggregate, and the
square/nonsquare character moment.  The result is the explicit sixth-power
inequality immediately preceding the extraction of sixth roots in Section 9,
pp. 111--112, of Friedlander--Iwaniec, *Ternary quadratic forms with rational
zeros* (JTNB 22 (2010), DOI 10.5802/jtnb.706).
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The inner numerator sum to which FI apply the cubic power. -/
def friedlanderIwaniecInnerJacobiSum
    (alpha : ℕ → ℝ) (M n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    alpha m * (jacobiSym (m : ℤ) n : ℝ)

/-- The real phase which turns the cube of an inner sum into its absolute
cube. -/
def friedlanderIwaniecCubicPhase
    (alpha : ℕ → ℝ) (M n : ℕ) : ℝ :=
  Real.sign (friedlanderIwaniecInnerJacobiSum alpha M n)

theorem abs_friedlanderIwaniecCubicPhase_le_one
    (alpha : ℕ → ℝ) (M n : ℕ) :
    |friedlanderIwaniecCubicPhase alpha M n| ≤ 1 := by
  unfold friedlanderIwaniecCubicPhase
  rcases Real.sign_apply_eq (friedlanderIwaniecInnerJacobiSum alpha M n) with
    h | h | h <;> rw [h] <;> norm_num

/-- Multiplication by the selected phase realizes the absolute cube exactly,
including at zero. -/
theorem friedlanderIwaniecCubicPhase_mul_pow_three
    (alpha : ℕ → ℝ) (M n : ℕ) :
    friedlanderIwaniecCubicPhase alpha M n *
        friedlanderIwaniecInnerJacobiSum alpha M n ^ 3 =
      |friedlanderIwaniecInnerJacobiSum alpha M n| ^ 3 := by
  let x := friedlanderIwaniecInnerJacobiSum alpha M n
  change Real.sign x * x ^ 3 = |x| ^ 3
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    ring
  · rw [hx]
    norm_num
  · rw [Real.sign_of_pos hx, abs_of_pos hx]
    ring

/-- Exact phase-weighted cubic regrouping, with the remaining character
column expressed through the real column used by the Pólya--Vinogradov
second-moment theorem. -/
theorem ofReal_sum_phase_mul_inner_pow_three_eq_cubicAggregate
    (alpha : ℕ → ℝ) (M N : ℕ) :
    Complex.ofReal
        (∑ n ∈ (Finset.Icc 1 N).filter Odd,
          friedlanderIwaniecCubicPhase alpha M n *
            friedlanderIwaniecInnerJacobiSum alpha M n ^ 3) =
      ∑ ell ∈ Finset.Icc 1 (M ^ 3),
        friedlanderIwaniecCubicCoefficient M ell
            (fun m ↦ (alpha m : ℂ)) *
          Complex.ofReal
            (friedlanderIwaniecOddJacobiColumn
              (friedlanderIwaniecCubicPhase alpha M) N ell) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    friedlanderIwaniecInnerJacobiSum,
    friedlanderIwaniecOddJacobiColumn, Complex.ofReal_intCast]
  simp_rw [pow_three_sum_alpha_mul_jacobi_eq_cubicAggregate]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _hell
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Cauchy plus the exact cubic `tauThree` aggregate bounds the squared
sum of absolute cubes by the unweighted Jacobi column moment. -/
theorem sum_abs_friedlanderIwaniecInnerJacobiSum_cube_sq_le
    (alpha : ℕ → ℝ) (M N : ℕ)
    (halpha : ∀ m ∈ Finset.Icc 1 M, |alpha m| ≤ 1) :
    (∑ n ∈ (Finset.Icc 1 N).filter Odd,
        |friedlanderIwaniecInnerJacobiSum alpha M n| ^ 3) ^ 2 ≤
      (M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 *
        friedlanderIwaniecOddJacobiColumnSecondMoment
          (friedlanderIwaniecCubicPhase alpha M) N (M ^ 3) := by
  let O := (Finset.Icc 1 N).filter Odd
  let phase := friedlanderIwaniecCubicPhase alpha M
  let F : ℕ → ℂ := fun ell ↦
    Complex.ofReal (friedlanderIwaniecOddJacobiColumn phase N ell)
  have halphaC : ∀ m ∈ Finset.Icc 1 M, ‖(alpha m : ℂ)‖ ≤ 1 := by
    intro m hm
    simpa only [Complex.norm_real, Real.norm_eq_abs] using halpha m hm
  have hphaseSum :
      (∑ n ∈ O, phase n *
          friedlanderIwaniecInnerJacobiSum alpha M n ^ 3) =
        ∑ n ∈ O, |friedlanderIwaniecInnerJacobiSum alpha M n| ^ 3 := by
    apply Finset.sum_congr rfl
    intro n _hn
    exact friedlanderIwaniecCubicPhase_mul_pow_three alpha M n
  have haggregate :
      Complex.ofReal
          (∑ n ∈ O, phase n *
            friedlanderIwaniecInnerJacobiSum alpha M n ^ 3) =
        ∑ ell ∈ Finset.Icc 1 (M ^ 3),
          friedlanderIwaniecCubicCoefficient M ell
              (fun m ↦ (alpha m : ℂ)) * F ell := by
    exact ofReal_sum_phase_mul_inner_pow_three_eq_cubicAggregate alpha M N
  have hcauchy :=
    norm_sum_friedlanderIwaniecCubicCoefficient_mul_sq_le_cube_log
      M (fun m ↦ (alpha m : ℂ)) F halphaC
  have hmoment :
      (∑ ell ∈ Finset.Icc 1 (M ^ 3), ‖F ell‖ ^ 2) =
        friedlanderIwaniecOddJacobiColumnSecondMoment phase N (M ^ 3) := by
    unfold friedlanderIwaniecOddJacobiColumnSecondMoment
    apply Finset.sum_congr rfl
    intro ell _hell
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← hphaseSum]
  calc
    (∑ n ∈ O, phase n *
        friedlanderIwaniecInnerJacobiSum alpha M n ^ 3) ^ 2 =
        ‖Complex.ofReal
          (∑ n ∈ O, phase n *
            friedlanderIwaniecInnerJacobiSum alpha M n ^ 3)‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ‖∑ ell ∈ Finset.Icc 1 (M ^ 3),
          friedlanderIwaniecCubicCoefficient M ell
              (fun m ↦ (alpha m : ℂ)) * F ell‖ ^ 2 := by
      rw [haggregate]
    _ ≤ (M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 *
        ∑ ell ∈ Finset.Icc 1 (M ^ 3), ‖F ell‖ ^ 2 := hcauchy
    _ = (M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 *
        friedlanderIwaniecOddJacobiColumnSecondMoment phase N (M ^ 3) := by
      rw [hmoment]

/-- Fully assembled one-sided sixth-power estimate from FI Section 9.  It
contains all arithmetic and finite-inequality content before the final
sixth-root and logarithmic normalization. -/
theorem abs_friedlanderIwaniecJacobiBilinear_pow_six_le
    (alpha beta : ℕ → ℝ) (M N : ℕ) (hN : 0 < N)
    (halpha : ∀ m ∈ Finset.Icc 1 M, |alpha m| ≤ 1)
    (hbetaEven : ∀ n : ℕ, Even n → beta n = 0)
    (hbeta : ∀ n : ℕ, |beta n| ≤ 1) :
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 ≤
      (N : ℝ) ^ 4 *
        ((M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6) *
          ((M : ℝ) ^ 3 * (N : ℝ) *
              (1 + Real.log (N : ℝ)) +
            6 * (N : ℝ) ^ 4) := by
  let S : ℝ := ∑ n ∈ (Finset.Icc 1 N).filter Odd,
    |friedlanderIwaniecInnerJacobiSum alpha M n| ^ 3
  have hholder :
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 3 ≤
        (N : ℝ) ^ 2 * S := by
    exact abs_friedlanderIwaniecJacobiBilinear_pow_three_le_odd
      alpha beta M N hbetaEven hbeta
  have hholderSq := pow_le_pow_left₀ (by positivity :
      0 ≤ |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 3)
    hholder 2
  have hSsq : S ^ 2 ≤
      (M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 *
        friedlanderIwaniecOddJacobiColumnSecondMoment
          (friedlanderIwaniecCubicPhase alpha M) N (M ^ 3) := by
    exact sum_abs_friedlanderIwaniecInnerJacobiSum_cube_sq_le
      alpha M N halpha
  have hmoment := friedlanderIwaniecOddJacobiColumnSecondMoment_cube_le
    (friedlanderIwaniecCubicPhase alpha M) M N hN
      (abs_friedlanderIwaniecCubicPhase_le_one alpha M)
  have hNpow : 0 ≤ (N : ℝ) ^ 4 := by positivity
  have hcubic :
      0 ≤ (M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 := by
    positivity
  calc
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 =
        (|friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 3) ^ 2 := by ring
    _ ≤ ((N : ℝ) ^ 2 * S) ^ 2 := hholderSq
    _ = (N : ℝ) ^ 4 * S ^ 2 := by ring
    _ ≤ (N : ℝ) ^ 4 *
        ((M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 *
          friedlanderIwaniecOddJacobiColumnSecondMoment
            (friedlanderIwaniecCubicPhase alpha M) N (M ^ 3)) :=
      mul_le_mul_of_nonneg_left hSsq hNpow
    _ ≤ (N : ℝ) ^ 4 *
        ((M : ℝ) ^ 3 * (1 + Real.log (M : ℝ)) ^ 6 *
          ((M : ℝ) ^ 3 * (N : ℝ) *
              (1 + Real.log (N : ℝ)) +
            6 * (N : ℝ) ^ 4)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmoment hcubic) hNpow
    _ = _ := by ring

end

end PellPaper
