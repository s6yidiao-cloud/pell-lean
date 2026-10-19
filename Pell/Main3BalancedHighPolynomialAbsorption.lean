import Pell.Main3BalancedCeilingParameters
import Pell.UniformBalancedScaleAbsorption
import Mathlib.Tactic

/-!
# Uniform absorption of the main3 high-box coefficient polynomials

The high balanced-box envelope retains two explicit coefficient factors.  At
`B = ceil(theta^2)` both are bounded by the cube of a single
`K * theta^7 * (1 + log(2Y))` factor.  Three applications packed as a cube of
the canonical uniform absorption lemma then cost only
`Y^(1/(800*theta^2))`.

This file contains only parameter arithmetic.  It does not import or assert a
box-counting estimate.
-/

namespace PellPaper

open Filter

noncomputable section

/-- A convenient fixed coefficient dominating both numerical constants in
the high balanced envelope. -/
def main3BalancedHighAbsorptionConstant : ℝ := 8000000000000

/-- The near-square degree ceiling is very crudely bounded by `theta^3`; this
form is convenient for uniform polynomial absorption. -/
theorem main3BalancedDegree_add_one_le_theta_cube
    (theta : ℝ) (htheta : 3 ≤ theta) :
    (main3BalancedDegree theta : ℝ) + 1 ≤ theta ^ 3 := by
  have hdegree := (main3BalancedDegree_nearSquare theta).2
  have hthetaSqTwo : (2 : ℝ) ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have htwoThetaSq : 2 * theta ^ 2 ≤ theta * theta ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg theta)
  exact le_of_lt <| calc
    (main3BalancedDegree theta : ℝ) + 1 < theta ^ 2 + 2 := by linarith
    _ ≤ 2 * theta ^ 2 := by nlinarith
    _ ≤ theta * theta ^ 2 := htwoThetaSq
    _ = theta ^ 3 := by ring

/-- Both coefficient factors in the high balanced union envelope are bounded
by the cube of one canonical absorption factor. -/
theorem main3BalancedHighEnvelope_coefficients_le_absorption_cube
    (theta Y : ℝ) (htheta : 3 ≤ theta) (hY : 1 ≤ Y) :
    let B : ℕ := main3BalancedDegree theta
    let H0 : ℕ := 2 * (B + 1)
    let L : ℝ := 1 + Real.log (2 * Y)
    let A : ℝ := main3BalancedHighAbsorptionConstant * theta ^ 7 * L
    1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤ A ^ 3 ∧
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤ A ^ 3 := by
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let L : ℝ := 1 + Real.log (2 * Y)
  let K : ℝ := main3BalancedHighAbsorptionConstant
  let A : ℝ := K * theta ^ 7 * L
  change
    1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤ A ^ 3 ∧
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤ A ^ 3
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have htheta0 : 0 ≤ theta := zero_le_one.trans hthetaOne
  have hthetaPowOne (n : ℕ) : (1 : ℝ) ≤ theta ^ n :=
    one_le_pow₀ hthetaOne
  have htheta3le7 : theta ^ 3 ≤ theta ^ 7 := by
    calc
      theta ^ 3 = theta ^ 3 * 1 := by ring
      _ ≤ theta ^ 3 * theta ^ 4 :=
        mul_le_mul_of_nonneg_left (hthetaPowOne 4) (pow_nonneg htheta0 _)
      _ = theta ^ 7 := by ring
  have htheta4le7 : theta ^ 4 ≤ theta ^ 7 := by
    calc
      theta ^ 4 = theta ^ 4 * 1 := by ring
      _ ≤ theta ^ 4 * theta ^ 3 :=
        mul_le_mul_of_nonneg_left (hthetaPowOne 3) (pow_nonneg htheta0 _)
      _ = theta ^ 7 := by ring
  have htheta6le21 : theta ^ 6 ≤ theta ^ 21 := by
    calc
      theta ^ 6 = theta ^ 6 * 1 := by ring
      _ ≤ theta ^ 6 * theta ^ 15 :=
        mul_le_mul_of_nonneg_left (hthetaPowOne 15) (pow_nonneg htheta0 _)
      _ = theta ^ 21 := by ring
  have hLone : (1 : ℝ) ≤ L := by
    dsimp [L]
    have htwoY : (1 : ℝ) ≤ 2 * Y := by linarith
    exact le_add_of_nonneg_right (Real.log_nonneg htwoY)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hBplus : (B : ℝ) + 1 ≤ theta ^ 3 := by
    simpa only [B] using main3BalancedDegree_add_one_le_theta_cube theta htheta
  have hB : (B : ℝ) ≤ theta ^ 3 := by linarith
  have hH0 : (H0 : ℝ) ≤ 2 * theta ^ 3 := by
    dsimp [H0]
    push_cast
    nlinarith
  have hthetaB : theta * (B : ℝ) ≤ theta ^ 4 := by
    calc
      theta * (B : ℝ) ≤ theta * theta ^ 3 :=
        mul_le_mul_of_nonneg_left hB htheta0
      _ = theta ^ 4 := by ring
  have hbracket :
      (H0 : ℝ) + 96 * theta * (B : ℝ) + 16 ≤
        114 * theta ^ 7 := by
    calc
      (H0 : ℝ) + 96 * theta * (B : ℝ) + 16 ≤
          2 * theta ^ 3 + 96 * theta ^ 4 + 16 * 1 := by
        linarith
      _ ≤ 2 * theta ^ 7 + 96 * theta ^ 7 + 16 * theta ^ 7 := by
        gcongr
        exact hthetaPowOne 7
      _ = 114 * theta ^ 7 := by ring
  have hfirstA :
      1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤ A := by
    calc
      1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤
          153672 * theta ^ 7 := by nlinarith
      _ ≤ K * theta ^ 7 := by
        gcongr
        norm_num [K, main3BalancedHighAbsorptionConstant]
      _ ≤ K * theta ^ 7 * L := by
        have hKtheta0 : 0 ≤ K * theta ^ 7 := by
          dsimp [K, main3BalancedHighAbsorptionConstant]
          positivity
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hLone hKtheta0)
      _ = A := by rfl
  have hAone : (1 : ℝ) ≤ A := by
    dsimp [A, K, main3BalancedHighAbsorptionConstant]
    have htheta7 := hthetaPowOne 7
    nlinarith [mul_le_mul htheta7 hLone (by norm_num : (0 : ℝ) ≤ 1)
      (pow_nonneg htheta0 7)]
  have hA0 : 0 ≤ A := zero_le_one.trans hAone
  have hAleCube : A ≤ A ^ 3 := by
    calc
      A = A * 1 := by ring
      _ ≤ A * A ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hAone) hA0
      _ = A ^ 3 := by ring
  have hfirst :
      1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤ A ^ 3 :=
    hfirstA.trans hAleCube
  have hsecondPre :
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤
        K * theta ^ 6 * L ^ 3 := by
    calc
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤
          7864320000000 * (theta ^ 3) ^ 2 * L ^ 3 := by
        gcongr
      _ = 7864320000000 * theta ^ 6 * L ^ 3 := by ring
      _ ≤ K * theta ^ 6 * L ^ 3 := by
        gcongr
        norm_num [K, main3BalancedHighAbsorptionConstant]
  have hKcube : K ≤ K ^ 3 := by
    norm_num [K, main3BalancedHighAbsorptionConstant]
  have hsecond :
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤ A ^ 3 := by
    calc
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤
          K * theta ^ 6 * L ^ 3 := hsecondPre
      _ ≤ K ^ 3 * theta ^ 6 * L ^ 3 := by
        gcongr
      _ ≤ K ^ 3 * theta ^ 21 * L ^ 3 := by
        have hfactor0 : 0 ≤ K ^ 3 * L ^ 3 := by
          dsimp [K, main3BalancedHighAbsorptionConstant]
          positivity
        calc
          K ^ 3 * theta ^ 6 * L ^ 3 = (K ^ 3 * L ^ 3) * theta ^ 6 := by ring
          _ ≤ (K ^ 3 * L ^ 3) * theta ^ 21 :=
            mul_le_mul_of_nonneg_left htheta6le21 hfactor0
          _ = K ^ 3 * theta ^ 21 * L ^ 3 := by ring
      _ = A ^ 3 := by
        dsimp [A]
        ring
  exact ⟨hfirst, hsecond⟩

/-- Uniform natural-scale absorption of both high-envelope coefficient
factors.  The stronger smallness premise reserves one third of the displayed
`1/800` exponent before cubing. -/
theorem eventually_main3BalancedHighEnvelope_coefficients_le_rpow
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        let B : ℕ := main3BalancedDegree theta
        let H0 : ℕ := 2 * (B + 1)
        let L : ℝ := 1 + Real.log (2 * (Y : ℝ))
        1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤
            (Y : ℝ) ^ (((1 : ℝ) / 800) / theta ^ 2) ∧
          7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤
            (Y : ℝ) ^ (((1 : ℝ) / 800) / theta ^ 2) := by
  have hreal := eventually_uniform_theta_seventh_log_le_balanced_rpow
    c ((1 : ℝ) / 2400) main3BalancedHighAbsorptionConstant
      hc (by norm_num) (by norm_num [main3BalancedHighAbsorptionConstant]) hsmall
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop 2] with Y habsorb hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let L : ℝ := 1 + Real.log (2 * y)
  let A : ℝ := main3BalancedHighAbsorptionConstant * theta ^ 7 * L
  let q : ℝ := ((1 : ℝ) / 2400) / theta ^ 2
  let q3 : ℝ := ((1 : ℝ) / 800) / theta ^ 2
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : (1 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have htwoY : (1 : ℝ) ≤ 2 * y := by linarith
    exact add_nonneg (by norm_num) (Real.log_nonneg htwoY)
  have hcoeff :=
    main3BalancedHighEnvelope_coefficients_le_absorption_cube
      theta y htheta (by dsimp [y]; exact_mod_cast (show 1 ≤ Y by omega))
  have hA : A ≤ y ^ q := by
    simpa only [A, L, y, q] using habsorb theta htheta hadmissible
  have hA0 : 0 ≤ A := by
    dsimp [A, main3BalancedHighAbsorptionConstant]
    positivity
  have hcube : A ^ 3 ≤ (y ^ q) ^ 3 :=
    pow_le_pow_left₀ hA0 hA 3
  have hpower : (y ^ q) ^ 3 = y ^ q3 := by
    rw [← Real.rpow_mul_natCast hypos.le]
    dsimp [q, q3]
    congr 1
    ring
  change
    1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) ≤ y ^ q3 ∧
      7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3 ≤ y ^ q3
  exact ⟨hcoeff.1.trans (hcube.trans_eq hpower),
    hcoeff.2.trans (hcube.trans_eq hpower)⟩

end

end PellPaper
