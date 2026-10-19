import Pell.Main3BalancedFinalElementary
import Pell.Main3LargeAnalyticElementaryLowerEvidence
import Pell.UniformSquarePartRestoration

/-!
# Final main3 assembly from the elementary square-sieve route

This module keeps the already checked direct-unbalanced and square-part
bookkeeping, but replaces the balanced estimate by the unconditional
elementary square-sieve theorem.  The concrete elementary large-analytic
endpoint is imported above and discharges the exact no-Weil
proposition-valued interface used by the final assembly.
-/

open Filter
open scoped BigOperators

namespace PellPaper

noncomputable section

/-- The exact large-analytic block estimate needed by the elementary final
assembly.  Unlike the older lower-evidence interface, this statement does not
take `OneVariableQuadraticWeilDegreeBound` as an argument. -/
def Main3LargeAnalyticBlockSumEstimateElementaryInput : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ c : ℝ, 0 < c →
      10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ((∑ i ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)
          ≤ C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2))

/-- The elementary balanced estimate, the proved direct-unbalanced estimate,
and the explicit no-Weil large-analytic input give the squarefree dyadic
estimate.  The constant is `35 + 2 + C`. -/
theorem exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput) :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c →
        10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
            C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨C, hC, hLargeAll⟩ := hLarge
  refine ⟨37 + C, by linarith, ?_⟩
  intro c hc hsmall
  have hBalanced :=
    eventually_main3BalancedDyadicFactorTuples_card_le_elementary c hc hsmall
  have hDirect :=
    eventually_main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
      shiftedSquareCongruenceWindowAverageAssertion_proved c hc hsmall
  have hLargeAt := hLargeAll c hc hsmall
  filter_upwards [hBalanced, hDirect, hLargeAt] with Y hBalancedY hDirectY hLargeY
  intro theta htheta hadmissible
  have hthetaCover : 0 ≤ theta + 1 / 4 := by linarith
  have hCountNat :=
    squarefreeDyadicExceptionalCount_le_balanced_add_admissibleUnbalanced
      (Y := Y) (R := main3BalancedR theta Y) hthetaCover
  have hUnbalancedNat :=
    card_admissibleUnbalancedDyadicFactorTuples_le_main3EnlargedDirect_add_largeAnalytic
      theta Y
  have hCountNat' :
      squarefreeDyadicExceptionalCount (theta + 1 / 4) Y ≤
        (balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card +
        ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) +
          ∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) := by
    omega
  have hCount :
      (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
        ((balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card : ℝ) +
        (((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) +
          ((∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) := by
    exact_mod_cast hCountNat'
  have hBalanced' := hBalancedY theta htheta hadmissible
  have hDirect' := hDirectY theta htheta hadmissible
  have hLarge' := hLargeY theta htheta hadmissible
  let y : ℝ := Y
  let b : ℝ := 1 - 1 / (400 * theta ^ 2)
  calc
    (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
        ((balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card : ℝ) +
        (((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) +
          ((∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) :=
      hCount
    _ ≤ 35 * y ^ b + (2 * y ^ b + C * y ^ b) := by
      simpa only [y, b] using
        add_le_add hBalanced' (add_le_add hDirect' hLarge')
    _ = (37 + C) * y ^ b := by ring

/-- Fixed-`c` specialization of the elementary squarefree dyadic estimate. -/
theorem eventually_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
          C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨C, hC, hAll⟩ :=
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
      hLarge
  exact ⟨C, hC, hAll c hc hsmall⟩

theorem exists_pos_uniform_squarefreeDyadicCoverSum_le_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        UniformAdmissible ((1 : ℝ) / 1600) theta (Y : ℝ) →
        (∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
          C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨Csf, hCsf, hsfAll⟩ :=
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
      hLarge
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

/-- The elementary squarefree estimate restores arbitrary square parts with
the absolute saving `1 / 6400`. -/
theorem uniformDyadicAllRadicandEstimate_one_div_6400_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput) :
    UniformDyadicAllRadicandEstimate ((1 : ℝ) / 6400) := by
  classical
  obtain ⟨Csf, hCsf, hcoverAll⟩ :=
    exists_pos_uniform_squarefreeDyadicCoverSum_le_elementary_of_large
      hLarge
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

/-- The elementary no-Weil large-block input implies the global uniform
exceptional-set estimate. -/
theorem uniformExceptionalEstimate_one_div_6400_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput) :
    UniformExceptionalEstimate ((1 : ℝ) / 6400) :=
  uniformExceptionalEstimate_of_uniformDyadicAllRadicandEstimate
    (uniformDyadicAllRadicandEstimate_one_div_6400_elementary_of_large hLarge)

/-- Conditional final assembly at the exact remaining no-Weil large-block
interface.  The concrete elementary large-analytic endpoint will discharge
this sole argument. -/
theorem realQuadraticOrderClassAverageAssertion_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput) :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_uniformDyadicAllRadicandEstimate
    (uniformDyadicAllRadicandEstimate_one_div_6400_elementary_of_large hLarge)

/-- The proved elementary large-analytic endpoint has exactly the raw shape
used by this assembly. -/
theorem main3LargeAnalyticBlockSumEstimateElementaryInput_proved :
    Main3LargeAnalyticBlockSumEstimateElementaryInput := by
  simpa only [Main3LargeAnalyticBlockSumEstimateElementaryInput,
    Main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary] using
    main3LargeAnalyticBlockSumEstimateLowerEvidence_elementary_proved

/-- Unconditional squarefree dyadic estimate from the elementary route. -/
theorem exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c →
        10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
            C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) :=
  exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
    main3LargeAnalyticBlockSumEstimateElementaryInput_proved

/-- Unconditional squarefree dyadic-cover estimate from the elementary
route. -/
theorem exists_pos_uniform_squarefreeDyadicCoverSum_le_elementary :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        UniformAdmissible ((1 : ℝ) / 1600) theta (Y : ℝ) →
        (∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
          (squarefreeDyadicExceptionalCount
            (theta + (1 : ℝ) / 4) (2 ^ k) : ℝ)) ≤
          C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) :=
  exists_pos_uniform_squarefreeDyadicCoverSum_le_elementary_of_large
    main3LargeAnalyticBlockSumEstimateElementaryInput_proved

/-- Unconditional arbitrary-radicand dyadic estimate with saving
`1 / 6400`. -/
theorem uniformDyadicAllRadicandEstimate_one_div_6400_elementary_proved :
    UniformDyadicAllRadicandEstimate ((1 : ℝ) / 6400) :=
  uniformDyadicAllRadicandEstimate_one_div_6400_elementary_of_large
    main3LargeAnalyticBlockSumEstimateElementaryInput_proved

/-- Unconditional uniform exceptional-set estimate with saving
`1 / 6400`. -/
theorem uniformExceptionalEstimate_one_div_6400_elementary_proved :
    UniformExceptionalEstimate ((1 : ℝ) / 6400) :=
  uniformExceptionalEstimate_one_div_6400_elementary_of_large
    main3LargeAnalyticBlockSumEstimateElementaryInput_proved

/-- The unconditional all-order class-average assertion, i.e. the remaining
part of Theorem 1.1, obtained without formalizing the Weil bound. -/
theorem realQuadraticOrderClassAverageAssertion :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_elementary_of_large
    main3LargeAnalyticBlockSumEstimateElementaryInput_proved

end

end PellPaper
