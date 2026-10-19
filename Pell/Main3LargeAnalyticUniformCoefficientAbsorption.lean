import Pell.Main3LargeAnalyticShiftWeightAbsorption
import Pell.Main3UnbalancedEnlargedDirectScaleAbsorption
import Mathlib.Tactic

/-!
# Uniform absorption of the elementary main3 large-analytic coefficients

This candidate closes the elementary coefficient endpoint left after a
fixed-key/fixed-cell arithmetic estimate.  Any fixed monomial in `theta` and
`1 + log (2 * A_a * Y)` is absorbed uniformly into an arbitrarily small
additional power `Y^(epsilon/theta^2)`.  The cardinality of the actual
large-analytic dyadic index finset is included through the canonical exact
index-count estimate.

The dyadic index family itself contains the radius
`Y^(1/(100*theta^2))`; this unavoidable exponent is retained explicitly.
No point-counting or square-sieve premise is introduced here.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Every fixed monomial in `theta` and `1 + log (2Y)` is uniformly absorbed
by an arbitrarily small moving power.  The admissibility constant is chosen
before the eventual cutoff and before `theta`. -/
theorem exists_pos_eventually_uniform_fixedThetaLogPolynomial_le_rpow_candidate
    (K epsilon : ℝ) (thetaDegree logDegree : ℕ)
    (hepsilon : 0 < epsilon) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c₀ * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        K * theta ^ thetaDegree *
            (1 + Real.log (2 * (Y : ℝ))) ^ logDegree ≤
          (Y : ℝ) ^ (epsilon / theta ^ 2) := by
  let q : ℕ := thetaDegree + logDegree + 1
  let qReal : ℝ := q
  let K₀ : ℝ := max 1 K
  let kappa : ℝ := epsilon / qReal
  let c₀ : ℝ := Real.sqrt (kappa / 20)
  have hq : 0 < q := by dsimp [q]; omega
  have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne'
  have hqReal : 0 < qReal := by
    dsimp [qReal]
    exact_mod_cast hq
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    exact zero_lt_one.trans_le (le_max_left 1 K)
  have hK₀One : 1 ≤ K₀ := by
    dsimp [K₀]
    exact le_max_left 1 K
  have hKK₀ : K ≤ K₀ := by
    dsimp [K₀]
    exact le_max_right 1 K
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    positivity
  have hc₀Small : 10 * c₀ ^ 2 ≤ kappa := by
    have hkappaNonneg : 0 ≤ kappa / 20 := by positivity
    dsimp [c₀]
    rw [Real.sq_sqrt hkappaNonneg]
    linarith [hkappa]
  have habsorbReal :=
    eventually_uniform_theta_seventh_log_le_balanced_rpow
      c₀ kappa K₀ hc₀ hkappa hK₀ hc₀Small
  have habsorbNat := tendsto_natCast_atTop_atTop.eventually habsorbReal
  refine ⟨c₀, hc₀, ?_⟩
  filter_upwards [habsorbNat, eventually_ge_atTop 2] with Y habsorb hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let L : ℝ := 1 + Real.log (2 * y)
  let A : ℝ := K₀ * theta ^ 7 * L
  have hypos : 0 < y := by dsimp [y]; positivity
  have hy : 0 ≤ y := hypos.le
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have htheta0 : 0 ≤ theta := zero_le_one.trans hthetaOne
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos (by linarith)
  have hLone : (1 : ℝ) ≤ L := by
    dsimp [L, y]
    have hone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact le_add_of_nonneg_right (Real.log_nonneg hone)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ y ^ (kappa / theta ^ 2) := by
    simpa only [A, L, y] using habsorb theta htheta hadmissible
  have hKpow : K ≤ K₀ ^ q := by
    calc
      K ≤ K₀ := hKK₀
      _ = K₀ ^ (1 : ℕ) := (pow_one K₀).symm
      _ ≤ K₀ ^ q := pow_le_pow_right₀ hK₀One hqOne
  have hthetaDegree : thetaDegree ≤ 7 * q := by
    dsimp [q]
    omega
  have hlogDegree : logDegree ≤ q := by
    dsimp [q]
    omega
  have hthetaPow : theta ^ thetaDegree ≤ theta ^ (7 * q) :=
    pow_le_pow_right₀ hthetaOne hthetaDegree
  have hlogPow : L ^ logDegree ≤ L ^ q :=
    pow_le_pow_right₀ hLone hlogDegree
  have hcoefficient :
      K * theta ^ thetaDegree * L ^ logDegree ≤ A ^ q := by
    calc
      K * theta ^ thetaDegree * L ^ logDegree ≤
          K₀ ^ q * theta ^ (7 * q) * L ^ q := by
        gcongr
      _ = A ^ q := by
        dsimp [A]
        simp only [mul_pow, pow_mul]
  have hAq : A ^ q ≤ (y ^ (kappa / theta ^ 2)) ^ q :=
    pow_le_pow_left₀ hA0 hA q
  have hpowerIdentity :
      (y ^ (kappa / theta ^ 2)) ^ q =
        y ^ (epsilon / theta ^ 2) := by
    rw [← Real.rpow_mul_natCast hy]
    congr 1
    dsimp [kappa, qReal]
    field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne',
      hthetaSqPos.ne']
  simpa only [L, y] using hcoefficient.trans (hAq.trans_eq hpowerIdentity)

/-- On an actual large-analytic index, the logarithm involving the
manuscript shift height is bounded by three copies of the standard dyadic
logarithm. -/
theorem main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_le_candidate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    1 + Real.log
        (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ)) ≤
      3 * (1 + Real.log (2 * (Y : ℝ))) := by
  let y : ℝ := Y
  let A : ℝ := main3LargeAnalyticShiftWeight h v
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (by omega : 1 ≤ Y)
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hiBroad := mem_unbalancedShiftedSquareDyadicCoverIndices.mp hiActive.1
  have ha0 : shiftedSquareA h v ≠ 0 :=
    shiftedSquareA_ne_zero hiBroad.1 (by omega)
  have ha0Real : (shiftedSquareA h v : ℝ) ≠ 0 := by exact_mod_cast ha0
  have hApos : 0 < A := by
    dsimp [A, main3LargeAnalyticShiftWeight]
    positivity
  have hA : A ≤ 4 * y := by
    have hbase := main3LargeAnalyticShiftWeight_le_four_mul_rpow_candidate
      htheta hY hi
    have hR := main3BalancedR_parameter_package theta Y htheta hY
    have hrY :
        (Y : ℝ) ^ main3BalancedRExponent theta ≤ (Y : ℝ) := by
      calc
        (Y : ℝ) ^ main3BalancedRExponent theta ≤
            (main3BalancedR theta Y : ℝ) := hR.2.1
        _ ≤ (Y : ℝ) := by exact_mod_cast hR.2.2.2
    dsimp [A, y]
    exact hbase.trans (mul_le_mul_of_nonneg_left hrY (by norm_num))
  have hyPow : y ^ 2 ≤ y ^ 3 :=
    pow_le_pow_right₀ hyone (by omega)
  have hargument : 2 * A * y ≤ (2 * y) ^ 3 := by
    calc
      2 * A * y = A * (2 * y) := by ring
      _ ≤ (4 * y) * (2 * y) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ = 8 * y ^ 2 := by ring
      _ ≤ 8 * y ^ 3 := mul_le_mul_of_nonneg_left hyPow (by norm_num)
      _ = (2 * y) ^ 3 := by ring
  have hlog : Real.log (2 * A * y) ≤ 3 * Real.log (2 * y) := by
    calc
      Real.log (2 * A * y) ≤ Real.log ((2 * y) ^ 3) :=
        Real.log_le_log (by positivity) hargument
      _ = 3 * Real.log (2 * y) := by rw [Real.log_pow]; norm_num
  change 1 + Real.log (2 * A * y) ≤ 3 * (1 + Real.log (2 * y))
  calc
    1 + Real.log (2 * A * y) ≤ 1 + 3 * Real.log (2 * y) := by
      linarith
    _ ≤ 3 + 3 * Real.log (2 * y) := by norm_num
    _ = 3 * (1 + Real.log (2 * y)) := by ring

/-- The actual large-analytic index cardinality, any fixed polynomial in
`theta`, and any fixed power of `1 + log (2*A_a*Y)` cost only
`Y^((1/100 + epsilon)/theta^2)`.  The `1/100` term is exactly the canonical
dyadic-radius exponent; `epsilon` is arbitrary and absorbs every remaining
fixed polynomial/logarithmic factor. -/
theorem exists_pos_eventually_main3LargeAnalytic_indexPolynomialLog_le_rpow_candidate
    (K epsilon : ℝ) (thetaDegree logDegree : ℕ)
    (hK : 0 < K) (hepsilon : 0 < epsilon) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c₀ * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ∀ h : ℤ, ∀ v D N : ℕ,
          (h, v, D, N) ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
          ((main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices
              theta Y).card : ℝ) *
              (K * theta ^ thetaDegree *
                (1 + Real.log
                  (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ))) ^
                    logDegree) ≤
            (Y : ℝ) ^ (((1 : ℝ) / 100 + epsilon) / theta ^ 2) := by
  let K₁ : ℝ := 512 * K * (3 : ℝ) ^ logDegree
  obtain ⟨c₀, hc₀, habsorb⟩ :=
    exists_pos_eventually_uniform_fixedThetaLogPolynomial_le_rpow_candidate
      K₁ epsilon (thetaDegree + 2) (logDegree + 2) hepsilon
  refine ⟨c₀, hc₀, ?_⟩
  filter_upwards [habsorb, eventually_ge_atTop 2] with Y habsorbY hY
  intro theta htheta hadmissible h v D N hi
  let y : ℝ := Y
  let delta : ℝ := main3BalancedRExponent theta
  let L : ℝ := 1 + Real.log (2 * y)
  let S : ℝ := 1 + Real.log
    (2 * main3LargeAnalyticShiftWeight h v * y)
  let P : ℝ := main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y
  let I : ℝ :=
    (main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y).card
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (by omega : 1 ≤ Y)
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have htheta0 : 0 ≤ theta := zero_le_one.trans hthetaOne
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos (by linarith)
  have hLone : (1 : ℝ) ≤ L := by
    dsimp [L, y]
    have hone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact le_add_of_nonneg_right (Real.log_nonneg hone)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hS : S ≤ 3 * L := by
    simpa only [S, L, y] using
      main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_le_candidate
        htheta hY hi
  have hS0 : 0 ≤ S := by
    dsimp [S, y]
    have hiLarge :=
      mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
    have hiActive :=
      mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
    have hiBroad :=
      mem_unbalancedShiftedSquareDyadicCoverIndices.mp hiActive.1
    have ha0 : shiftedSquareA h v ≠ 0 :=
      shiftedSquareA_ne_zero hiBroad.1 (by omega)
    have ha0Real : (shiftedSquareA h v : ℝ) ≠ 0 := by exact_mod_cast ha0
    have hargOne : (1 : ℝ) ≤
        2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ) := by
      unfold main3LargeAnalyticShiftWeight
      have habsOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
        have haInt : 1 ≤ |shiftedSquareA h v| := Int.one_le_abs ha0
        exact_mod_cast haInt
      have hYOne : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (by omega : 1 ≤ Y)
      nlinarith [mul_le_mul habsOne hYOne (by norm_num : (0 : ℝ) ≤ 1)
        (abs_nonneg (shiftedSquareA h v : ℝ))]
    linarith [Real.log_nonneg hargOne]
  have hSPow : S ^ logDegree ≤
      (3 : ℝ) ^ logDegree * L ^ logDegree := by
    calc
      S ^ logDegree ≤ (3 * L) ^ logDegree :=
        pow_le_pow_left₀ hS0 hS logDegree
      _ = (3 : ℝ) ^ logDegree * L ^ logDegree := by rw [mul_pow]
  have hP : P ≤
      32 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := by
    simpa only [P, y, delta, L, Nat.cast_mul, Nat.cast_ofNat] using
      main3UnbalancedEnlargedDyadicIndexScaleProduct_cast_le
        theta Y htheta hY
  have hINat :=
    card_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices_le theta Y
  have hIP : I ≤ 4 * P := by
    dsimp [I, P]
    exact_mod_cast hINat
  have hI : I ≤
      128 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := by
    calc
      I ≤ 4 * P := hIP
      _ ≤ 4 *
          (32 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hP (by norm_num)
      _ = 128 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := by
        ring
  have hI0 : 0 ≤ I := by dsimp [I]; positivity
  have hthetaProduct : (theta + 1) * (theta + 2) ≤ 4 * theta ^ 2 := by
    have h1 : theta + 1 ≤ 2 * theta := by linarith
    have h2 : theta + 2 ≤ 2 * theta := by linarith
    calc
      (theta + 1) * (theta + 2) ≤ (2 * theta) * (2 * theta) :=
        mul_le_mul h1 h2 (by linarith) (by positivity)
      _ = 4 * theta ^ 2 := by ring
  have hpoly0 : 0 ≤ K * theta ^ thetaDegree * S ^ logDegree := by
    positivity
  have hcoefficient :
      K₁ * theta ^ (thetaDegree + 2) * L ^ (logDegree + 2) ≤
        y ^ (epsilon / theta ^ 2) := by
    simpa only [K₁, y, L] using habsorbY theta htheta hadmissible
  have hpolyBound :
      K * theta ^ thetaDegree * S ^ logDegree ≤
        K * theta ^ thetaDegree *
          ((3 : ℝ) ^ logDegree * L ^ logDegree) :=
    mul_le_mul_of_nonneg_left hSPow (by positivity)
  have hI' : I ≤ 128 * y ^ delta * (4 * theta ^ 2) * L ^ 2 := by
    have hprefactor :
        128 * y ^ delta * ((theta + 1) * (theta + 2)) ≤
          128 * y ^ delta * (4 * theta ^ 2) :=
      mul_le_mul_of_nonneg_left hthetaProduct (by positivity)
    have hwithLog :
        (128 * y ^ delta * ((theta + 1) * (theta + 2))) * L ^ 2 ≤
          (128 * y ^ delta * (4 * theta ^ 2)) * L ^ 2 :=
      mul_le_mul_of_nonneg_right hprefactor (pow_nonneg hL0 _)
    calc
      I ≤ 128 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := hI
      _ = (128 * y ^ delta * ((theta + 1) * (theta + 2))) * L ^ 2 := by
        ring
      _ ≤ (128 * y ^ delta * (4 * theta ^ 2)) * L ^ 2 := hwithLog
      _ = 128 * y ^ delta * (4 * theta ^ 2) * L ^ 2 := by ring
  have hcombined :
      I * (K * theta ^ thetaDegree * S ^ logDegree) ≤
        y ^ delta *
          (K₁ * theta ^ (thetaDegree + 2) * L ^ (logDegree + 2)) := by
    calc
      I * (K * theta ^ thetaDegree * S ^ logDegree) ≤
          (128 * y ^ delta * (4 * theta ^ 2) * L ^ 2) *
            (K * theta ^ thetaDegree * S ^ logDegree) :=
        mul_le_mul_of_nonneg_right hI' hpoly0
      _ ≤ (128 * y ^ delta * (4 * theta ^ 2) * L ^ 2) *
            (K * theta ^ thetaDegree *
              ((3 : ℝ) ^ logDegree * L ^ logDegree)) :=
        mul_le_mul_of_nonneg_left hpolyBound (by positivity)
      _ = y ^ delta *
          (K₁ * theta ^ (thetaDegree + 2) * L ^ (logDegree + 2)) := by
        dsimp [K₁]
        simp only [pow_add]
        ring
  change I * (K * theta ^ thetaDegree * S ^ logDegree) ≤
    y ^ (((1 : ℝ) / 100 + epsilon) / theta ^ 2)
  calc
    I * (K * theta ^ thetaDegree * S ^ logDegree) ≤
        y ^ delta *
          (K₁ * theta ^ (thetaDegree + 2) * L ^ (logDegree + 2)) :=
      hcombined
    _ ≤ y ^ delta * y ^ (epsilon / theta ^ 2) :=
      mul_le_mul_of_nonneg_left hcoefficient (Real.rpow_nonneg hypos.le _)
    _ = y ^ (delta + epsilon / theta ^ 2) := by
      rw [Real.rpow_add hypos]
    _ = y ^ (((1 : ℝ) / 100 + epsilon) / theta ^ 2) := by
      congr 1
      dsimp [delta, main3BalancedRExponent]
      field_simp [hthetaSqPos.ne']

end

end PellPaper
