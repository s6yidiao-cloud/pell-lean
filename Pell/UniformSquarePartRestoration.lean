import Pell.Main3LargeAnalyticBlockSumLowerEvidence
import Pell.ShiftedSquareCongruenceWindowAverageProof
import Pell.UniformDyadicAllRadicandBridge
import Pell.DyadicSquarePartTailPower
import Pell.BudgetedSmallSquarePartCover
import Pell.SmallRootBudgetNat
import Pell.UniformBalancedScaleAbsorption
import Mathlib.Tactic

/-!
# Uniform square-part restoration from the squarefree main3 estimate

This file performs the class-(A) bookkeeping between the narrow
large-analytic lower-evidence boundary and the already checked uniform
all-radicand/global bridge.  No additional analytic premise is introduced.
-/

open Filter
open scoped BigOperators

namespace PellPaper

noncomputable section

/-- A scale between `sqrt X / 2` and `2X` loses at most a fixed factor four
in the square root of `log/loglog`.  Together with `theta < 2*uniformQ theta`,
this turns `UniformAdmissible c theta X` into the direct theta-bound with
coefficient `8c` at the nearby scale. -/
theorem theta_le_eight_mul_of_uniformAdmissible_of_sqrt_half_le_two_mul
    {c theta X Z : ℝ}
    (hc : 0 ≤ c)
    (hX : Real.exp 12 ≤ X)
    (hZlower : Real.sqrt X / 2 ≤ Z)
    (hZupper : Z ≤ 2 * X)
    (h : UniformAdmissible c theta X) :
    theta ≤ (8 * c) * Real.sqrt
      (Real.log Z / Real.log (Real.log Z)) := by
  have hexpPos : 0 < Real.exp (12 : ℝ) := Real.exp_pos _
  have hXpos : 0 < X := hexpPos.trans_le hX
  have hlogX : 12 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log hexpPos hX
  have hlogXpos : 0 < Real.log X := by linarith
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hhalfpos : 0 < Real.sqrt X / 2 := div_pos hsqrtXpos (by norm_num)
  have hZpos : 0 < Z := hhalfpos.trans_le hZlower
  have hlogZlower : Real.log X / 4 ≤ Real.log Z := by
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      have hlogTwo' :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hlogTwo' ⊢
      exact hlogTwo'
    have hlogSqrtDiv :
        Real.log (Real.sqrt X / 2) = Real.log X / 2 - Real.log 2 := by
      rw [Real.log_div (Real.sqrt_ne_zero'.mpr hXpos) (by norm_num),
        Real.log_sqrt hXpos.le]
    have hquarter : Real.log X / 4 ≤ Real.log (Real.sqrt X / 2) := by
      rw [hlogSqrtDiv]
      linarith
    exact hquarter.trans (Real.log_le_log hhalfpos hZlower)
  have hlogZpos : 0 < Real.log Z := by
    have : 0 < Real.log X / 4 := div_pos hlogXpos (by norm_num)
    exact this.trans_le hlogZlower
  have hloglogZpos : 0 < Real.log (Real.log Z) := by
    apply Real.log_pos
    have : 3 ≤ Real.log X / 4 := by linarith
    linarith
  have hloglogXpos : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    linarith
  have hlogZupper : Real.log Z ≤ 2 * Real.log X := by
    calc
      Real.log Z ≤ Real.log (2 * X) := Real.log_le_log hZpos hZupper
      _ = Real.log 2 + Real.log X := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
      _ ≤ 2 * Real.log X := by
        have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log X := by
          have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
            have hlogTwo' :=
              Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            norm_num at hlogTwo' ⊢
            exact hlogTwo'
          linarith
        linarith
  have hloglogZupper :
      Real.log (Real.log Z) ≤ 2 * Real.log (Real.log X) := by
    calc
      Real.log (Real.log Z) ≤ Real.log (2 * Real.log X) :=
        Real.log_le_log hlogZpos hlogZupper
      _ = Real.log 2 + Real.log (Real.log X) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogXpos.ne']
      _ ≤ 2 * Real.log (Real.log X) := by
        have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (Real.log X) := by
          have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
            have hlogTwo' :=
              Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            norm_num at hlogTwo' ⊢
            exact hlogTwo'
          have honeLe : (1 : ℝ) ≤ Real.log (Real.log X) := by
            apply (Real.le_log_iff_exp_le hlogXpos).2
            exact (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 12)).trans hlogX
          exact hlogTwoLeOne.trans honeLe
        linarith
  have hratio :
      Real.log X / Real.log (Real.log X) ≤
        16 * (Real.log Z / Real.log (Real.log Z)) := by
    calc
      Real.log X / Real.log (Real.log X) ≤
          (4 * Real.log Z) / Real.log (Real.log X) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · exact hloglogXpos.le
      _ ≤ (4 * Real.log Z) / (Real.log (Real.log Z) / 2) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · linarith
      _ = 8 * (Real.log Z / Real.log (Real.log Z)) := by ring
      _ ≤ 16 * (Real.log Z / Real.log (Real.log Z)) := by
        have : 0 ≤ Real.log Z / Real.log (Real.log Z) :=
          div_nonneg hlogZpos.le hloglogZpos.le
        linarith
  have hratioZnonneg :
      0 ≤ Real.log Z / Real.log (Real.log Z) :=
    div_nonneg hlogZpos.le hloglogZpos.le
  have hsqrtRatio :
      Real.sqrt (Real.log X / Real.log (Real.log X)) ≤
        4 * Real.sqrt (Real.log Z / Real.log (Real.log Z)) := by
    calc
      Real.sqrt (Real.log X / Real.log (Real.log X)) ≤
          Real.sqrt (16 * (Real.log Z / Real.log (Real.log Z))) :=
        Real.sqrt_le_sqrt hratio
      _ = 4 * Real.sqrt (Real.log Z / Real.log (Real.log Z)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have hthetaQ : theta ≤ 2 * (uniformQ theta : ℝ) := by
    linarith [theta_add_half_le_two_mul_uniformQ theta]
  unfold UniformAdmissible at h
  calc
    theta ≤ 2 * (uniformQ theta : ℝ) := hthetaQ
    _ ≤ 2 * (c * Real.sqrt
        (Real.log X / Real.log (Real.log X))) := by gcongr
    _ ≤ 2 * (c * (4 * Real.sqrt
        (Real.log Z / Real.log (Real.log Z)))) := by
      gcongr
    _ = (8 * c) * Real.sqrt
        (Real.log Z / Real.log (Real.log Z)) := by ring

/-- Under the explicit main3 growth threshold, the ceiling threshold used
for the large-square-part tail still lies inside the stronger `1/8` root
budget.  The tail exponent is half of the squarefree saving. -/
theorem squarePartPowerThreshold_cast_le_budget_power_of_exp_growth
    {theta : ℝ} {Y : ℕ}
    (htheta : 3 ≤ theta)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    (squarePartPowerThreshold Y (1 / (800 * theta ^ 2)) : ℝ) ≤
      (Y : ℝ) ^ (((1 : ℝ) / 8) / (theta + 1)) := by
  let y : ℝ := Y
  let a : ℝ := 1 / (800 * theta ^ 2)
  let b : ℝ := ((1 : ℝ) / 8) / (theta + 1)
  let t : ℝ := y ^ a
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hthetaOnePos : 0 < theta + 1 := by linarith
  have hypos : 0 < y := by
    dsimp [y]
    exact (Real.exp_pos _).trans hYgrow
  have hlogY : 800 * theta ^ 2 < Real.log y := by
    have hlog := Real.log_lt_log (Real.exp_pos _) hYgrow
    simpa only [Real.log_exp, y] using hlog
  have hlogYpos : 0 < Real.log y := by
    have : 0 < 800 * theta ^ 2 := by positivity
    linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have honeLtLogMulA : 1 < Real.log y * a := by
    calc
      (1 : ℝ) = (800 * theta ^ 2) * a := by
        dsimp [a]
        field_simp
      _ < Real.log y * a := mul_lt_mul_of_pos_right hlogY ha
  have htTwo : 2 < t := by
    dsimp [t]
    rw [Real.rpow_def_of_pos hypos]
    exact Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr honeLtLogMulA)
  have htNonneg : 0 ≤ t := (lt_trans (by norm_num) htTwo).le
  have hthresholdTwo :
      (squarePartPowerThreshold Y a : ℝ) ≤ 2 * t := by
    have hceil : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one htNonneg
    unfold squarePartPowerThreshold
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hba : 1 / (16 * (theta + 1)) ≤ b - a := by
    dsimp [a, b]
    have hden1 : 0 < 8 * (theta + 1) := by positivity
    have hden2 : 0 < 16 * (theta + 1) := by positivity
    have hden3 : 0 < 800 * theta ^ 2 := by positivity
    rw [div_div]
    apply (le_sub_iff_add_le).2
    field_simp [hden1.ne', hden2.ne', hden3.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have honeLtLogMulGap : 1 < Real.log y * (b - a) := by
    have hbase : 1 < Real.log y * (1 / (16 * (theta + 1))) := by
      have hratio : 1 <
          (800 * theta ^ 2) * (1 / (16 * (theta + 1))) := by
        rw [one_div, mul_inv_rev, mul_assoc]
        field_simp
        nlinarith [sq_nonneg (theta - 3)]
      exact hratio.trans
        (mul_lt_mul_of_pos_right hlogY (by positivity))
    exact hbase.trans_le (mul_le_mul_of_nonneg_left hba hlogYpos.le)
  have hTwoGap : 2 ≤ y ^ (b - a) := by
    have hexp : Real.exp 1 < y ^ (b - a) := by
      rw [Real.rpow_def_of_pos hypos]
      exact Real.exp_lt_exp.mpr honeLtLogMulGap
    exact (Real.exp_one_gt_two.trans hexp).le
  have htwoT : 2 * t ≤ y ^ b := by
    calc
      2 * t = t * 2 := by ring
      _ ≤ t * y ^ (b - a) :=
        mul_le_mul_of_nonneg_left hTwoGap htNonneg
      _ = y ^ a * y ^ (b - a) := by rfl
      _ = y ^ (a + (b - a)) := (Real.rpow_add hypos a (b - a)).symm
      _ = y ^ b := by ring_nf
  simpa only [a, b, t, y] using hthresholdTwo.trans htwoT

/-- The same explicit growth threshold absorbs the ceiling in the natural
square-part cutoff at cost exactly a factor two.  This is the root-count
estimate used when summing the common squarefree dyadic-cover bound. -/
theorem squarePartPowerThreshold_cast_le_two_mul_rpow_of_exp_growth
    {theta : ℝ} {Y : ℕ}
    (htheta : 3 ≤ theta)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    (squarePartPowerThreshold Y (1 / (800 * theta ^ 2)) : ℝ) ≤
      2 * (Y : ℝ) ^ (1 / (800 * theta ^ 2)) := by
  let y : ℝ := Y
  let a : ℝ := 1 / (800 * theta ^ 2)
  let t : ℝ := y ^ a
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hypos : 0 < y := by
    dsimp [y]
    exact (Real.exp_pos _).trans hYgrow
  have hlogY : 800 * theta ^ 2 < Real.log y := by
    have hlog := Real.log_lt_log (Real.exp_pos _) hYgrow
    simpa only [Real.log_exp, y] using hlog
  have ha : 0 < a := by dsimp [a]; positivity
  have honeLtLogMulA : 1 < Real.log y * a := by
    calc
      (1 : ℝ) = (800 * theta ^ 2) * a := by
        dsimp [a]
        field_simp
      _ < Real.log y * a := mul_lt_mul_of_pos_right hlogY ha
  have htTwo : 2 < t := by
    dsimp [t]
    rw [Real.rpow_def_of_pos hypos]
    exact Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr honeLtLogMulA)
  have htNonneg : 0 ≤ t := (lt_trans (by norm_num) htTwo).le
  have hceil : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one htNonneg
  unfold squarePartPowerThreshold
  rw [Nat.cast_add, Nat.cast_one]
  simpa only [a, t, y] using (show (⌈t⌉₊ : ℝ) + 1 ≤ 2 * t by linarith)

/-- The eventual squarefree block estimate can be summed over every dyadic
scale below `2Y`, uniformly in the growing height.  Scales below `sqrt Y/2`
use the trivial interval-length estimate; every larger scale remains within
the nearby-scale admissibility window. -/
theorem exists_pos_uniform_squarefreeDyadicCoverSum_le_of_main3BlockEstimates
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        UniformAdmissible ((1 : ℝ) / 1600) theta (Y : ℝ) →
        (∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
          C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨Csf, hCsf, hsfAll⟩ :=
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_of_main3BlockEstimates
      hWeil haverage hLarge
  have hsfEventually :=
    hsfAll ((1 : ℝ) / 200) (by norm_num) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hsfEventually
  let denominatorFloor : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ) - 1
  have hdenominatorFloor : 0 < denominatorFloor := by
    dsimp [denominatorFloor]
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  let Ccover : ℝ := 1 + 4 * Csf / denominatorFloor
  have hCcover : 0 < Ccover := by
    dsimp [Ccover]
    positivity
  refine ⟨Ccover, hCcover, ?_⟩
  have hExpNat := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (Real.exp 12))
  filter_upwards [hExpNat, eventually_ge_atTop ((2 * N₀) ^ 2),
    eventually_ge_atTop 1] with Y hYexp hYN₀ hYone
  intro theta htheta hadmissible
  let y : ℝ := Y
  let p : ℝ := 1 - 1 / (400 * theta ^ 2)
  let K : ℕ := Nat.log 2 (2 * Y) + 1
  let M : ℕ := ⌊Real.sqrt y⌋₊
  let low : Finset ℕ :=
    (Finset.range K).filter (fun k => 2 * 2 ^ k ≤ M)
  let high : Finset ℕ :=
    (Finset.range K).filter (fun k => ¬ 2 * 2 ^ k ≤ M)
  have hypos : 0 < y := by
    dsimp [y]
    exact_mod_cast (show 0 < Y by omega)
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast hYone
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hdeltaPos : 0 < 1 / (400 * theta ^ 2) := by positivity
  have hdeltaHalf : 1 / (400 * theta ^ 2) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 400 * theta ^ 2)).2
    nlinarith [sq_nonneg (theta - 3)]
  have hp : 0 < p := by dsimp [p]; linarith
  have hpHalf : (1 / 2 : ℝ) ≤ p := by dsimp [p]; linarith
  have hpOne : p ≤ 1 := by dsimp [p]; linarith
  have hpartition :
      (∑ k ∈ Finset.range K,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) =
        (∑ k ∈ low,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) +
        (∑ k ∈ high,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) := by
    dsimp [low, high]
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hlow :
      (∑ k ∈ low,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤ M := by
    calc
      (∑ k ∈ low,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
          ∑ k ∈ low, ((2 ^ k : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact_mod_cast
          squarefreeDyadicExceptionalCount_le_scale
            (theta + (1 : ℝ) / 4) (2 ^ k)
      _ ≤ M := by
        simpa only [low] using sum_low_dyadic_scales_le K M
  have hsqrtN₀ : 2 * (N₀ : ℝ) ≤ Real.sqrt y := by
    calc
      2 * (N₀ : ℝ) = Real.sqrt ((2 * (N₀ : ℝ)) ^ 2) := by
        symm
        exact Real.sqrt_sq (by positivity)
      _ ≤ Real.sqrt y := by
        apply Real.sqrt_le_sqrt
        dsimp [y]
        exact_mod_cast hYN₀
  have hhighPoint : ∀ k ∈ high,
      (squarefreeDyadicExceptionalCount
        (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ) ≤
        Csf * ((2 ^ k : ℕ) : ℝ) ^ p := by
    intro k hk
    obtain ⟨hkK, hkHigh⟩ :=
      Finset.mem_filter.mp (by simpa only [high] using hk)
    have hkLog : k ≤ Nat.log 2 (2 * Y) := by
      have : k < K := Finset.mem_range.mp hkK
      dsimp [K] at this
      omega
    have htwoYne : 2 * Y ≠ 0 := by omega
    have hscaleUpperNat : 2 ^ k ≤ 2 * Y :=
      Nat.pow_le_of_le_log htwoYne hkLog
    have hscaleUpper : ((2 ^ k : ℕ) : ℝ) ≤ 2 * y := by
      dsimp [y]
      exact_mod_cast hscaleUpperNat
    have hMlt : M < 2 * 2 ^ k := lt_of_not_ge hkHigh
    have hsqrtLt : Real.sqrt y < (M : ℝ) + 1 := by
      dsimp [M]
      exact Nat.lt_floor_add_one _
    have hMSucc : (M : ℝ) + 1 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hMlt)
    have hscaleLower : Real.sqrt y / 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
      linarith
    have hN₀scaleReal : (N₀ : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      nlinarith
    have hN₀scale : N₀ ≤ 2 ^ k := by exact_mod_cast hN₀scaleReal
    have hthetaScale : theta ≤ ((1 : ℝ) / 200) * Real.sqrt
        (Real.log ((2 ^ k : ℕ) : ℝ) /
          Real.log (Real.log ((2 ^ k : ℕ) : ℝ))) := by
      have hnear :=
        theta_le_eight_mul_of_uniformAdmissible_of_sqrt_half_le_two_mul
          (c := (1 : ℝ) / 1600) (theta := theta) (X := y)
          (Z := ((2 ^ k : ℕ) : ℝ)) (by norm_num)
          (by simpa only [y] using hYexp) hscaleLower hscaleUpper
          (by simpa only [y] using hadmissible)
      norm_num at hnear ⊢
      exact hnear
    simpa only [p] using
      hN₀ (2 ^ k) hN₀scale theta htheta hthetaScale
  have hhigh :
      (∑ k ∈ high,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
        Csf * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
    calc
      (∑ k ∈ high,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
          ∑ k ∈ high, Csf * ((2 ^ k : ℕ) : ℝ) ^ p := by
        exact Finset.sum_le_sum hhighPoint
      _ ≤ ∑ k ∈ Finset.range K,
          Csf * ((2 ^ k : ℕ) : ℝ) ^ p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact (Finset.mem_filter.mp (by simpa only [high] using hk)).1
        · intro k _ _
          positivity
      _ = Csf * ∑ k ∈ Finset.range K,
          ((2 ^ k : ℕ) : ℝ) ^ p := by
        rw [Finset.mul_sum]
  have hdenominator :
      denominatorFloor ≤ (2 : ℝ) ^ p - 1 := by
    dsimp [denominatorFloor]
    have := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hpHalf
    linarith
  have hdenominatorPos : 0 < (2 : ℝ) ^ p - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hp)
  have htopNat : 2 ^ K ≤ 4 * Y := by
    dsimp [K]
    have h := two_pow_log_add_one_le_two_mul
      (N := 2 * Y) (by omega : 1 ≤ 2 * Y)
    omega
  have htop : ((2 ^ K : ℕ) : ℝ) ≤ 4 * y := by
    dsimp [y]
    exact_mod_cast htopNat
  have hfourPow : (4 : ℝ) ^ p ≤ 4 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hpOne)
  have htopPow : ((2 ^ K : ℕ) : ℝ) ^ p ≤ 4 * y ^ p := by
    calc
      ((2 ^ K : ℕ) : ℝ) ^ p ≤ (4 * y) ^ p :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) htop hp.le
      _ = (4 : ℝ) ^ p * y ^ p :=
        Real.mul_rpow (by norm_num) hypos.le
      _ ≤ 4 * y ^ p :=
        mul_le_mul_of_nonneg_right hfourPow (Real.rpow_nonneg hypos.le _)
  have hquotient :
      ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤
        (4 * y ^ p) / denominatorFloor :=
    div_le_div₀ (by positivity) htopPow hdenominatorFloor hdenominator
  have hhighFinal :
      (∑ k ∈ high,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
        Csf * ((4 * y ^ p) / denominatorFloor) := by
    calc
      (∑ k ∈ high,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
          Csf * ∑ k ∈ Finset.range K,
            ((2 ^ k : ℕ) : ℝ) ^ p := hhigh
      _ ≤ Csf *
          (((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) := by
        exact mul_le_mul_of_nonneg_left
          (sum_cast_two_pow_rpow_le p hp K) hCsf.le
      _ ≤ Csf * ((4 * y ^ p) / denominatorFloor) :=
        mul_le_mul_of_nonneg_left hquotient hCsf.le
  have hMreal : (M : ℝ) ≤ Real.sqrt y := by
    dsimp [M]
    exact Nat.floor_le (Real.sqrt_nonneg y)
  have hsqrtPower : Real.sqrt y ≤ y ^ p := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hyone hpHalf
  calc
    (∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
        (squarefreeDyadicExceptionalCount
          (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) =
        (∑ k ∈ Finset.range K,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) := by rfl
    _ = (∑ k ∈ low,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) +
        (∑ k ∈ high,
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) := hpartition
    _ ≤ (M : ℝ) + Csf * ((4 * y ^ p) / denominatorFloor) :=
      add_le_add hlow hhighFinal
    _ ≤ y ^ p + Csf * ((4 * y ^ p) / denominatorFloor) := by
      gcongr
      exact hMreal.trans hsqrtPower
    _ = Ccover * y ^ p := by
      dsimp [Ccover]
      ring
    _ = Ccover * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by rfl

/-- The three stated main3 inputs imply the uniform arbitrary-radicand dyadic
estimate with the absolute saving `1 / 6400`.  The witness
`cDyadic = 1 / 1600` is fixed before the scale and height quantifiers.

The squarefree saving is split evenly: one half pays for the number of
square-part roots and the other survives in the exponent.  The elementary
large-square-part tail has the same surviving exponent. -/
theorem uniformDyadicAllRadicandEstimate_one_div_6400_of_main3BlockEstimates
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    UniformDyadicAllRadicandEstimate ((1 : ℝ) / 6400) := by
  classical
  obtain ⟨Csf, hCsf, hcoverAll⟩ :=
    exists_pos_uniform_squarefreeDyadicCoverSum_le_of_main3BlockEstimates
      hWeil haverage hLarge
  have hgrowthReal :=
    eventually_uniform_exp_eightHundred_theta_sq_lt
      ((1 : ℝ) / 800) (by norm_num) (by norm_num)
  have hgrowthNat :=
    tendsto_natCast_atTop_atTop.eventually hgrowthReal
  unfold UniformDyadicAllRadicandEstimate
  refine ⟨by norm_num, by norm_num, (1 : ℝ) / 1600,
    2 * Csf + 2, by norm_num, by positivity, ?_⟩
  filter_upwards [hcoverAll, hgrowthNat, eventually_ge_atTop 1] with
      Y hcoverY hgrowthY hY
  intro theta htheta hadmissible
  have hthetaPos : 0 < theta := by linarith
  have hthetaNonneg : 0 ≤ theta := hthetaPos.le
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hQpos : 0 < (uniformQ theta : ℝ) := uniformQ_pos htheta
  have hthetaQ : theta ≤ 2 * (uniformQ theta : ℝ) := by
    linarith [theta_add_half_le_two_mul_uniformQ theta]
  have hthetaAdmissible :
      theta ≤ ((1 : ℝ) / 800) * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) := by
    unfold UniformAdmissible at hadmissible
    calc
      theta ≤ 2 * (uniformQ theta : ℝ) := hthetaQ
      _ ≤ 2 * (((1 : ℝ) / 1600) * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ)))) :=
        mul_le_mul_of_nonneg_left hadmissible (by norm_num)
      _ = ((1 : ℝ) / 800) * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) := by ring
  have hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ) :=
    hgrowthY theta htheta hthetaAdmissible
  let y : ℝ := Y
  let a : ℝ := 1 / (800 * theta ^ 2)
  let p : ℝ := 1 - 1 / (400 * theta ^ 2)
  let q : ℝ := 1 - a
  let target : ℝ :=
    1 - 2 * ((1 : ℝ) / 6400) / (uniformQ theta : ℝ) ^ 2
  let S : ℕ := squarePartPowerThreshold Y a
  have hypos : 0 < y := by
    dsimp [y]
    exact_mod_cast (show 0 < Y by omega)
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast hY
  have ha : 0 < a := by dsimp [a]; positivity
  have hSbudget :
      (S : ℝ) ≤ y ^ (((1 : ℝ) / 8) / (theta + 1)) := by
    dsimp [S, a, y]
    exact squarePartPowerThreshold_cast_le_budget_power_of_exp_growth
      htheta hYgrow
  have hbudgets : ∀ s : ℕ, 1 ≤ s → s < S →
      squarePartScaleBudget theta Y s :=
    all_squarePartScaleBudgets_of_nat_rpow_threshold
      (theta := theta) (lam := (1 : ℝ) / 8) (Y := Y) (S := S)
      hthetaNonneg hY (by simpa only [y] using hSbudget) (by norm_num)
  have hsmallNat :=
    dyadicSmallSquarePartExceptional_card_le_sum_dyadicBlocks_of_root_budgets
      hbudgets
  have hsmallCover :
      ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
        ∑ s ∈ Finset.Ico 1 S,
          ∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
            (squarefreeDyadicExceptionalCount
              (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ) := by
    exact_mod_cast hsmallNat
  have hcoverAt :
      (∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
        Csf * y ^ p := by
    simpa only [y, p] using hcoverY theta htheta hadmissible
  have hsmallRootCount :
      ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
        (((S - 1 : ℕ) : ℝ) * (Csf * y ^ p)) := by
    calc
      ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
          ∑ s ∈ Finset.Ico 1 S,
            ∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
              (squarefreeDyadicExceptionalCount
                (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ) := hsmallCover
      _ ≤ ∑ _s ∈ Finset.Ico 1 S, Csf * y ^ p := by
        exact Finset.sum_le_sum fun _ _ ↦ hcoverAt
      _ = (((S - 1 : ℕ) : ℝ) * (Csf * y ^ p)) := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hSroot : (S : ℝ) ≤ 2 * y ^ a := by
    dsimp [S, a, y]
    exact squarePartPowerThreshold_cast_le_two_mul_rpow_of_exp_growth
      htheta hYgrow
  have hrootCount : ((S - 1 : ℕ) : ℝ) ≤ 2 * y ^ a := by
    calc
      ((S - 1 : ℕ) : ℝ) ≤ (S : ℝ) := by
        exact_mod_cast Nat.sub_le S 1
      _ ≤ 2 * y ^ a := hSroot
  have hapq : a + p = q := by
    dsimp [a, p, q]
    ring
  have hsmallPower :
      ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
        2 * Csf * y ^ q := by
    calc
      ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
          ((S - 1 : ℕ) : ℝ) * (Csf * y ^ p) := hsmallRootCount
      _ ≤ (2 * y ^ a) * (Csf * y ^ p) :=
        mul_le_mul_of_nonneg_right hrootCount (by positivity)
      _ = 2 * Csf * y ^ (a + p) := by
        rw [Real.rpow_add hypos]
        ring
      _ = 2 * Csf * y ^ q := by rw [hapq]
  have hcountQ :
      (dyadicSquarePartExceptionalCount theta Y : ℝ) ≤
        (2 * Csf + 2) * y ^ q := by
    calc
      (dyadicSquarePartExceptionalCount theta Y : ℝ) ≤
          ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) +
            2 * y ^ q := by
        simpa only [S, q, a, y] using
          (dyadicSquarePartExceptionalCount_le_small_add_rpow theta hY a)
      _ ≤ 2 * Csf * y ^ q + 2 * y ^ q :=
        add_le_add hsmallPower le_rfl
      _ = (2 * Csf + 2) * y ^ q := by ring
  have hthetaSqLe :
      theta ^ 2 ≤ 4 * (uniformQ theta : ℝ) ^ 2 := by
    calc
      theta ^ 2 ≤ (2 * (uniformQ theta : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hthetaNonneg hthetaQ 2
      _ = 4 * (uniformQ theta : ℝ) ^ 2 := by ring
  have hdenominatorOrder :
      800 * theta ^ 2 ≤ 3200 * (uniformQ theta : ℝ) ^ 2 := by
    nlinarith
  have hreciprocal :
      1 / (3200 * (uniformQ theta : ℝ) ^ 2) ≤
        1 / (800 * theta ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hdenominatorOrder
  have htargetTerm :
      2 * ((1 : ℝ) / 6400) / (uniformQ theta : ℝ) ^ 2 =
        1 / (3200 * (uniformQ theta : ℝ) ^ 2) := by
    ring
  have hqTarget : q ≤ target := by
    dsimp [q, a, target]
    rw [htargetTerm]
    linarith
  have hpowerTarget : y ^ q ≤ y ^ target :=
    Real.rpow_le_rpow_of_exponent_le hyone hqTarget
  calc
    (dyadicSquarePartExceptionalCount theta Y : ℝ) ≤
        (2 * Csf + 2) * y ^ q := hcountQ
    _ ≤ (2 * Csf + 2) * y ^ target :=
      mul_le_mul_of_nonneg_left hpowerTarget (by positivity)
    _ = (2 * Csf + 2) * (Y : ℝ) ^
        (1 - 2 * ((1 : ℝ) / 6400) /
          (uniformQ theta : ℝ) ^ 2) := by rfl

/-- The corresponding uniform exceptional-set estimate, obtained through the
checked arbitrary-radicand dyadic-to-global bridge. -/
theorem uniformExceptionalEstimate_one_div_6400_of_main3BlockEstimates
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    UniformExceptionalEstimate ((1 : ℝ) / 6400) :=
  uniformExceptionalEstimate_of_uniformDyadicAllRadicandEstimate
    (uniformDyadicAllRadicandEstimate_one_div_6400_of_main3BlockEstimates
      hWeil haverage hLarge)

/-- The Theorem 1.1 all-order class-average headline follows from the two
named class-(B) inputs and the single stated class-(C) lower-evidence input. -/
theorem realQuadraticOrderClassAverageAssertion_of_main3BlockEstimates
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_uniformDyadicAllRadicandEstimate
    (uniformDyadicAllRadicandEstimate_one_div_6400_of_main3BlockEstimates
      hWeil haverage hLarge)

/-- The congruence-window premise in the preceding theorem is discharged by
its unconditional proof, leaving only the Weil and large-analytic inputs. -/
theorem uniformExceptionalEstimate_one_div_6400_of_Weil_and_largeAnalytic
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    UniformExceptionalEstimate ((1 : ℝ) / 6400) :=
  uniformExceptionalEstimate_one_div_6400_of_main3BlockEstimates
    hWeil shiftedSquareCongruenceWindowAverageAssertion_proved hLarge

/-- The all-order class-average headline no longer requires the
congruence-window average as an external premise. -/
theorem realQuadraticOrderClassAverageAssertion_of_Weil_and_largeAnalytic
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_main3BlockEstimates
    hWeil shiftedSquareCongruenceWindowAverageAssertion_proved hLarge

end

end PellPaper
