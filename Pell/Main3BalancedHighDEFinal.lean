import Pell.Main3BalancedHighDEEnvelope
import Pell.Main3BalancedHighPolynomialAbsorption
import Pell.Main3BalancedDyadicScaleCount
import Mathlib.Tactic

/-!
# Final main3 bound for the balanced high-DE union

The geometric high-box envelope, the four-scale count, and both explicit
coefficient factors are now canonical.  This file composes them and performs
the remaining real-power arithmetic.  The scale count and coefficient each
cost `Y^(1/(800*theta^2))`, while `Y/sqrt(R)` saves
`Y^(-1/(200*theta^2))`; hence the high union retains the saving
`1/(400*theta^2)`.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Uniform final estimate for the high-`DE` half of the main3 balanced
dyadic decomposition. -/
theorem eventually_main3BalancedHighDEBoxUnion_card_le
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ((main3BalancedHighDEBoxUnion theta Y
          (main3BalancedR theta Y)).card : ℝ) ≤
            3 * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  have hsmall400 : 10 * c ^ 2 ≤ (1 : ℝ) / 400 := by linarith
  have hsmall800 : 10 * c ^ 2 ≤ (1 : ℝ) / 800 := by linarith
  have henvelope :=
    eventually_main3BalancedHighDEBoxUnion_card_le_scaleProduct_mul_envelope
      hWeil c hc hsmall400
  have hscale :=
    eventually_main3Balanced_dyadicScaleProduct_cast_le_rpow
      c ((1 : ℝ) / 800) hc (by norm_num) hsmall800
  have hcoeff :=
    eventually_main3BalancedHighEnvelope_coefficients_le_rpow
      c hc hsmall
  filter_upwards [henvelope, hscale, hcoeff, eventually_ge_atTop 2] with
      Y hEnvelope hScale hCoeff hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let R : ℕ := main3BalancedR theta Y
  let T : ℝ := R
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let M : ℕ := main3BalancedM theta Y
  let K : ℝ := main3BalancedDyadicScaleProduct theta Y
  let L : ℝ := 1 + Real.log (2 * y)
  let P1 : ℝ := 1348 * ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16)
  let P2 : ℝ := 7864320000000 * ((B : ℝ) + 1) ^ 2 * L ^ 3
  let q : ℝ := ((1 : ℝ) / 800) / theta ^ 2
  let m : ℝ := 1 - 1 / (50 * theta ^ 2)
  let g : ℝ := 1 - 1 / (200 * theta ^ 2)
  let b : ℝ := 1 - 1 / (400 * theta ^ 2)
  have hyTwo : (2 : ℝ) ≤ y := by dsimp [y]; exact_mod_cast hY
  have hypos : 0 < y := by linarith
  have hyone : 1 ≤ y := by linarith
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hK : K ≤ y ^ q := by
    simpa only [K, y, q] using hScale theta htheta hadmissible
  have hCoeff' := hCoeff theta htheta hadmissible
  have hP1 : P1 ≤ y ^ q := by
    simpa only [P1, H0, B, y, q] using hCoeff'.1
  have hP2 : P2 ≤ y ^ q := by
    simpa only [P2, L, B, y, q] using hCoeff'.2
  have hMpackage := main3BalancedM_sharp_bounds theta Y htheta hY
  have hM : (M : ℝ) ≤ 2 * y ^ m := by
    simpa only [M, y, m, main3BalancedMExponent] using hMpackage.2.2
  have hRpackage := main3BalancedR_parameter_package theta Y htheta hY
  have hTpos : 0 < T := by
    dsimp [T, R]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hRpackage.1)
  have hrT : y ^ main3BalancedRExponent theta ≤ T := by
    simpa only [y, T, R] using hRpackage.2.1
  have hsqrtPower :
      Real.sqrt (y ^ main3BalancedRExponent theta) =
        y ^ (main3BalancedRExponent theta / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hypos.le]
    congr 1
    ring
  have hsqrtLower :
      y ^ (main3BalancedRExponent theta / 2) ≤ Real.sqrt T := by
    rw [← hsqrtPower]
    exact Real.sqrt_le_sqrt hrT
  have hgeomRaw :
      y / Real.sqrt T ≤
        y ^ (1 - main3BalancedRExponent theta / 2) := by
    calc
      y / Real.sqrt T ≤
          y / y ^ (main3BalancedRExponent theta / 2) :=
        div_le_div_of_nonneg_left hypos.le
          (Real.rpow_pos_of_pos hypos _) hsqrtLower
      _ = y ^ (1 - main3BalancedRExponent theta / 2) := by
        rw [Real.rpow_sub hypos, Real.rpow_one]
  have hgeom : y / Real.sqrt T ≤ y ^ g := by
    have hexponent :
        1 - main3BalancedRExponent theta / 2 = g := by
      dsimp [g, main3BalancedRExponent]
      field_simp [hthetaSqPos.ne']
      ring
    rw [← hexponent]
    exact hgeomRaw
  have hq0 : 0 ≤ y ^ q := Real.rpow_nonneg hypos.le _
  have hm0 : 0 ≤ y ^ m := Real.rpow_nonneg hypos.le _
  have hg0 : 0 ≤ y ^ g := Real.rpow_nonneg hypos.le _
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hP10 : 0 ≤ P1 := by
    dsimp [P1, H0]
    positivity
  have hP20 : 0 ≤ P2 := by
    dsimp [P2, L]
    have hlog0 : 0 ≤ 1 + Real.log (2 * y) := by
      have hone : (1 : ℝ) ≤ 2 * y := by linarith
      exact add_nonneg (by norm_num) (Real.log_nonneg hone)
    positivity
  have hfirstExponent : q + m + q ≤ b := by
    dsimp [q, m, b]
    field_simp [hthetaSqPos.ne']
    nlinarith
  have hsecondExponent : q + q + g = b := by
    dsimp [q, g, b]
    field_simp [hthetaSqPos.ne']
    ring
  have hfirst : K * ((M : ℝ) * P1) ≤ 2 * y ^ b := by
    calc
      K * ((M : ℝ) * P1) ≤ y ^ q * ((2 * y ^ m) * y ^ q) := by
        gcongr
      _ = 2 * y ^ (q + m + q) := by
        rw [Real.rpow_add hypos, Real.rpow_add hypos]
        ring
      _ ≤ 2 * y ^ b :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hyone hfirstExponent)
          (by norm_num)
  have hsecond : K * (P2 * (y / Real.sqrt T)) ≤ y ^ b := by
    calc
      K * (P2 * (y / Real.sqrt T)) ≤ y ^ q * (y ^ q * y ^ g) := by
        gcongr
      _ = y ^ (q + q + g) := by
        rw [Real.rpow_add hypos, Real.rpow_add hypos]
        ring
      _ = y ^ b := by rw [hsecondExponent]
  have hEnvelope' :
      ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) ≤
        K * ((M : ℝ) * P1 + P2 * (y / Real.sqrt T)) := by
    have hraw := hEnvelope theta htheta hadmissible
    dsimp only at hraw
    calc
      ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) =
          ((main3BalancedHighDEBoxUnion theta Y
            (main3BalancedR theta Y)).card : ℝ) := by rfl
      _ ≤ _ := hraw
      _ = K * ((M : ℝ) * P1 + P2 * (y / Real.sqrt T)) := by
        dsimp [K, M, P1, P2, L, y, T, R, B, H0,
          main3BalancedDyadicScaleProduct]
        push_cast
        ring
  calc
    ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) ≤
        K * ((M : ℝ) * P1 + P2 * (y / Real.sqrt T)) := hEnvelope'
    _ = K * ((M : ℝ) * P1) + K * (P2 * (y / Real.sqrt T)) := by ring
    _ ≤ 2 * y ^ b + y ^ b := add_le_add hfirst hsecond
    _ = 3 * y ^ b := by ring

end

end PellPaper
