import Pell.Main3UnbalancedEnlargedDirectRangeSummation
import Pell.UniformBalancedScaleAbsorption
import Mathlib.Tactic

/-!
# Uniform absorption for the enlarged main3 direct unbalanced sum

The direct index count contains two binary scale counts.  The second is at
the genuinely enlarged height

`dyadicFactorHeight (theta+1/4) Y * main3BalancedR theta Y`.

This module first proves a logarithmic bound for that scale, then an explicit
polynomial/logarithmic bound for the complete index product, and finally
absorbs the resulting direct-sum coefficient in the canonical growing-`theta`
range.  The sole analytic input is the existing transparent proposition
`ShiftedSquareCongruenceWindowAverageAssertion`.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- The second enlarged source scale, including the original-`theta` radius,
has a uniform linear-logarithmic binary scale count. -/
theorem dyadicScaleCount_main3UnbalancedEnlargedSecondHeight_cast_le
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (dyadicScaleCount
      (dyadicFactorHeight (theta + 1 / 4) Y *
        main3BalancedR theta Y) : ℝ) ≤
      4 * (theta + 2) *
        (1 + Real.log (((2 * Y : ℕ) : ℝ))) := by
  let x : ℝ := ((2 * Y : ℕ) : ℝ)
  let a : ℝ := theta + 1 / 4
  let z : ℝ := x ^ a
  let H : ℕ := dyadicFactorHeight (theta + 1 / 4) Y
  let R : ℕ := main3BalancedR theta Y
  let Q : ℕ := H * R
  have hx : (4 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.mul_le_mul_left 2 hY
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have haone : (1 : ℝ) ≤ a := by
    dsimp [a]
    linarith
  have hzpos : 0 < z := by
    dsimp [z]
    exact Real.rpow_pos_of_pos hxpos _
  have hzfour : (4 : ℝ) ≤ z := by
    calc
      (4 : ℝ) ≤ x := hx
      _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hxone haone
      _ = z := rfl
  have hceil : (H : ℝ) < z + 1 := by
    dsimp [H, dyadicFactorHeight, z, x, a]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have hH : (H : ℝ) ≤ 2 * z := by
    linarith
  have hRnat : R ≤ Y := by
    dsimp [R]
    exact (main3BalancedR_parameter_package theta Y htheta hY).2.2.2
  have hR : (R : ℝ) ≤ x := by
    have hRY : (R : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hRnat
    dsimp [x]
    push_cast
    linarith
  have hQ : (Q : ℝ) ≤ 2 * (z * x) := by
    calc
      (Q : ℝ) = (H : ℝ) * (R : ℝ) := by simp [Q]
      _ ≤ (2 * z) * x := by gcongr
      _ = 2 * (z * x) := by ring
  have hzx : (16 : ℝ) ≤ z * x := by
    nlinarith [mul_le_mul hzfour hx (by norm_num : (0 : ℝ) ≤ 4)
      (by linarith : (0 : ℝ) ≤ z)]
  have hquadratic : 0 ≤ (z * x - 3) * (z * x + 1) :=
    mul_nonneg (sub_nonneg.mpr (by linarith)) (by linarith)
  have hQplus : (((Q + 1 : ℕ) : ℝ)) ≤ (z * x) ^ 2 := by
    push_cast
    nlinarith
  have hlogQ :
      Real.log (((Q + 1 : ℕ) : ℝ)) ≤
        2 * (a + 1) * Real.log x := by
    calc
      Real.log (((Q + 1 : ℕ) : ℝ)) ≤ Real.log ((z * x) ^ 2) :=
        Real.log_le_log (by positivity) hQplus
      _ = 2 * Real.log (z * x) := by rw [Real.log_pow]; norm_num
      _ = 2 * (Real.log z + Real.log x) := by
        rw [Real.log_mul hzpos.ne' hxpos.ne']
      _ = 2 * (a + 1) * Real.log x := by
        rw [show Real.log z = a * Real.log x by
          dsimp [z]
          exact Real.log_rpow hxpos a]
        ring
  have hscale :=
    dyadicScaleCount_cast_le_one_add_two_mul_log_add_one Q
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have haUpper : a + 1 ≤ theta + 2 := by
    dsimp [a]
    linarith [show (1 : ℝ) / 4 ≤ 1 by norm_num]
  have haLog :
      (a + 1) * Real.log x ≤ (theta + 2) * Real.log x :=
    mul_le_mul_of_nonneg_right haUpper hlogx0
  have hone : (1 : ℝ) ≤ 4 * (theta + 2) := by linarith
  change (dyadicScaleCount Q : ℝ) ≤
    4 * (theta + 2) * (1 + Real.log x)
  calc
    (dyadicScaleCount Q : ℝ) ≤
        1 + 2 * Real.log (((Q + 1 : ℕ) : ℝ)) := hscale
    _ ≤ 1 + 2 * (2 * (a + 1) * Real.log x) := by linarith
    _ ≤ 4 * (theta + 2) +
        4 * ((theta + 2) * Real.log x) := by nlinarith
    _ = 4 * (theta + 2) * (1 + Real.log x) := by ring

/-- Explicit real polynomial/logarithmic bound for the complete enlarged
direct index-scale product.  Both heights use `theta+1/4`; the leading radius
is bounded using its original-`theta` exponent. -/
theorem main3UnbalancedEnlargedDyadicIndexScaleProduct_cast_le
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y : ℝ) ≤
      32 * (Y : ℝ) ^ main3BalancedRExponent theta *
        (theta + 1) * (theta + 2) *
          (1 + Real.log (((2 * Y : ℕ) : ℝ))) ^ 2 := by
  let r : ℝ := (Y : ℝ) ^ main3BalancedRExponent theta
  let R : ℝ := (main3BalancedR theta Y : ℝ)
  let S : ℝ :=
    (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) : ℝ)
  let T : ℝ :=
    (dyadicScaleCount
      (dyadicFactorHeight (theta + 1 / 4) Y *
        main3BalancedR theta Y) : ℝ)
  let L : ℝ := 1 + Real.log (((2 * Y : ℕ) : ℝ))
  have hR : R ≤ 2 * r := by
    simpa only [R, r] using
      (main3BalancedR_parameter_package theta Y htheta hY).2.2.1
  have hS : S ≤ 4 * (theta + 1) * L := by
    simpa only [S, L] using
      dyadicScaleCount_main3FactorHeight_cast_le theta Y htheta hY
  have hT : T ≤ 4 * (theta + 2) * L := by
    simpa only [T, L] using
      dyadicScaleCount_main3UnbalancedEnlargedSecondHeight_cast_le
        theta Y htheta hY
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hthetaOne0 : 0 ≤ theta + 1 := by linarith
  have hthetaTwo0 : 0 ≤ theta + 2 := by linarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have hone : (1 : ℝ) ≤ (((2 * Y : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact add_nonneg (by norm_num) (Real.log_nonneg hone)
  have hproduct :
      R * (S * T) ≤
        (2 * r) *
          ((4 * (theta + 1) * L) * (4 * (theta + 2) * L)) := by
    gcongr
  calc
    (main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y : ℝ) =
        R * (S * T) := by
      simp [main3UnbalancedEnlargedDyadicIndexScaleProduct, R, S, T]
    _ ≤
        (2 * r) *
          ((4 * (theta + 1) * L) * (4 * (theta + 2) * L)) := hproduct
    _ = 32 * (Y : ℝ) ^ main3BalancedRExponent theta *
        (theta + 1) * (theta + 2) *
          (1 + Real.log (((2 * Y : ℕ) : ℝ))) ^ 2 := by
      dsimp [r, L]
      ring

/-- The canonical direct finite sum after inserting the explicit enlarged
index-product estimate. -/
theorem main3UnbalancedEnlargedDirectBlockSum_cast_le_polynomial_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ),
        3 ≤ theta → 2 ≤ Y →
        ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
          (256 * C * (theta + 1) ^ 2 * (theta + 2) *
              (1 + Real.log (((2 * Y : ℕ) : ℝ))) ^ 3) *
            (Y : ℝ) ^ main3BalancedRExponent theta *
            (7 * Real.sqrt (Y : ℝ) +
              3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2))) := by
  obtain ⟨C, hC, hsum⟩ :=
    main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
      haverage
  refine ⟨C, hC, ?_⟩
  intro theta Y htheta hY
  let P : ℕ := main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y
  let r : ℝ := (Y : ℝ) ^ main3BalancedRExponent theta
  let L : ℝ := 1 + Real.log (((2 * Y : ℕ) : ℝ))
  let S : ℝ := 7 * Real.sqrt (Y : ℝ) +
    3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2))
  have hbase := hsum theta Y htheta hY
  have hP : (P : ℝ) ≤
      32 * r * (theta + 1) * (theta + 2) * L ^ 2 := by
    simpa only [P, r, L] using
      main3UnbalancedEnlargedDyadicIndexScaleProduct_cast_le
        theta Y htheta hY
  have hcount : ((4 * P : ℕ) : ℝ) ≤
      128 * r * (theta + 1) * (theta + 2) * L ^ 2 := by
    push_cast
    nlinarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have hone : (1 : ℝ) ≤ (((2 * Y : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact add_nonneg (by norm_num) (Real.log_nonneg hone)
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hE0 : 0 ≤ C * (S * (2 * (theta + 1) * L)) := by
    positivity
  change
    ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
      (squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
      (256 * C * (theta + 1) ^ 2 * (theta + 2) * L ^ 3) *
        r * S
  calc
    ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
      (squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
        ((4 * P : ℕ) : ℝ) *
          (C * (S * (2 * (theta + 1) * L))) := by
      simpa only [P, S, L] using hbase
    _ ≤ (128 * r * (theta + 1) * (theta + 2) * L ^ 2) *
          (C * (S * (2 * (theta + 1) * L))) :=
      mul_le_mul_of_nonneg_right hcount hE0
    _ = (256 * C * (theta + 1) ^ 2 * (theta + 2) * L ^ 3) *
          r * S := by ring

/-- Eventual uniform power saving for the complete direct active block sum.
The cutoff in `Y` may depend on the fixed congruence-window assertion and on
`c`, but every admissible `theta` is quantified after that cutoff. -/
theorem eventually_main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
          2 * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨C, hC, hsum⟩ :=
    main3UnbalancedEnlargedDirectBlockSum_cast_le_polynomial_of_congruenceWindowAverage
      haverage
  let K : ℝ := max 1 (14336 * C)
  have hKpos : 0 < K := by
    exact zero_lt_one.trans_le (le_max_left 1 (14336 * C))
  have habsReal :=
    eventually_uniform_theta_seventh_log_le_balanced_rpow
      c ((1 : ℝ) / 2400) K hc (by norm_num) hKpos hsmall
  have habsNat := tendsto_natCast_atTop_atTop.eventually habsReal
  filter_upwards [habsNat, eventually_ge_atTop 2] with Y habsorb hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let L : ℝ := 1 + Real.log (((2 * Y : ℕ) : ℝ))
  let delta : ℝ := main3BalancedRExponent theta
  let s : ℝ := 1 - 1 / (32 * theta ^ 2)
  let q : ℝ := ((1 : ℝ) / 2400) / theta ^ 2
  let q3 : ℝ := ((1 : ℝ) / 800) / theta ^ 2
  let b : ℝ := 1 - 1 / (400 * theta ^ 2)
  let A : ℝ := K * theta ^ 7 * L
  let P : ℝ := 256 * C * (theta + 1) ^ 2 * (theta + 2) * L ^ 3
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have hLone : (1 : ℝ) ≤ L := by
    dsimp [L]
    have hone : (1 : ℝ) ≤ (((2 * Y : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact le_add_of_nonneg_right (Real.log_nonneg hone)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ y ^ q := by
    simpa only [A, K, L, y, q, Nat.cast_mul, Nat.cast_ofNat] using
      habsorb theta htheta hadmissible
  have hcube : A ^ 3 ≤ (y ^ q) ^ 3 :=
    pow_le_pow_left₀ hA0 hA 3
  have hcubePower : (y ^ q) ^ 3 = y ^ q3 := by
    rw [← Real.rpow_mul_natCast hypos.le]
    dsimp [q, q3]
    congr 1
    ring
  have hthetaProduct :
      (theta + 1) ^ 2 * (theta + 2) ≤ 8 * theta ^ 3 := by
    have h1 : theta + 1 ≤ 2 * theta := by linarith
    have h2 : theta + 2 ≤ 2 * theta := by linarith
    calc
      (theta + 1) ^ 2 * (theta + 2) ≤
          (2 * theta) ^ 2 * (2 * theta) := by gcongr
      _ = 8 * theta ^ 3 := by ring
  have hthetaPow : theta ^ 3 ≤ theta ^ 21 := by
    calc
      theta ^ 3 = theta ^ 3 * 1 := by ring
      _ ≤ theta ^ 3 * theta ^ 18 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hthetaOne)
          (pow_nonneg hthetaPos.le _)
      _ = theta ^ 21 := by ring
  have hKC : 14336 * C ≤ K ^ 3 := by
    have hCK : 14336 * C ≤ K := le_max_right _ _
    have hKone : (1 : ℝ) ≤ K := le_max_left _ _
    have hKcube : K ≤ K ^ 3 := by
      calc
        K = K * 1 := by ring
        _ ≤ K * K ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hKone) hKpos.le
        _ = K ^ 3 := by ring
    exact hCK.trans hKcube
  have hsevenP : 7 * P ≤ A ^ 3 := by
    have hpre :
        7 * P ≤ 14336 * C * theta ^ 3 * L ^ 3 := by
      calc
        7 * P = (1792 * C * L ^ 3) *
            ((theta + 1) ^ 2 * (theta + 2)) := by
          dsimp [P]
          ring
        _ ≤ (1792 * C * L ^ 3) * (8 * theta ^ 3) :=
          mul_le_mul_of_nonneg_left hthetaProduct (by positivity)
        _ = 14336 * C * theta ^ 3 * L ^ 3 := by ring
    have hcore :
        14336 * C * theta ^ 3 ≤ K ^ 3 * theta ^ 21 := by
      calc
        14336 * C * theta ^ 3 ≤ K ^ 3 * theta ^ 3 :=
          mul_le_mul_of_nonneg_right hKC (pow_nonneg hthetaPos.le _)
        _ ≤ K ^ 3 * theta ^ 21 :=
          mul_le_mul_of_nonneg_left hthetaPow (pow_nonneg hKpos.le _)
    calc
      7 * P ≤ 14336 * C * theta ^ 3 * L ^ 3 := hpre
      _ ≤ K ^ 3 * theta ^ 21 * L ^ 3 :=
        mul_le_mul_of_nonneg_right hcore (pow_nonneg hL0 _)
      _ = A ^ 3 := by dsimp [A]; ring
  have hthreeP : 3 * P ≤ A ^ 3 := by
    exact (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 7) hP0).trans
      hsevenP
  have hsevenPower : 7 * P ≤ y ^ q3 :=
    hsevenP.trans (hcube.trans_eq hcubePower)
  have hthreePower : 3 * P ≤ y ^ q3 :=
    hthreeP.trans (hcube.trans_eq hcubePower)
  have hfirstExponent : q3 + delta + (1 : ℝ) / 2 ≤ b := by
    dsimp [q3, delta, b, main3BalancedRExponent]
    field_simp [hthetaSqPos.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have hsecondExponent : q3 + delta + s ≤ b := by
    dsimp [q3, delta, s, b, main3BalancedRExponent]
    field_simp [hthetaSqPos.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have hfirstPower :
      y ^ q3 * y ^ delta * Real.sqrt y ≤ y ^ b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hypos, ← Real.rpow_add hypos]
    exact Real.rpow_le_rpow_of_exponent_le hyone hfirstExponent
  have hsecondPower : y ^ q3 * y ^ delta * y ^ s ≤ y ^ b := by
    rw [← Real.rpow_add hypos, ← Real.rpow_add hypos]
    exact Real.rpow_le_rpow_of_exponent_le hyone hsecondExponent
  have hsum' := hsum theta Y htheta hY
  change
    ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
      (squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
      2 * y ^ b
  calc
    ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
      (squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
        P * y ^ delta *
          (7 * Real.sqrt y + 3 * y ^ s) := by
      simpa only [P, y, delta, s, L] using hsum'
    _ = (7 * P) * y ^ delta * Real.sqrt y +
          (3 * P) * y ^ delta * y ^ s := by ring
    _ ≤ y ^ q3 * y ^ delta * Real.sqrt y +
          y ^ q3 * y ^ delta * y ^ s := by
      gcongr
    _ ≤ y ^ b + y ^ b := add_le_add hfirstPower hsecondPower
    _ = 2 * y ^ b := by ring

end

end PellPaper
