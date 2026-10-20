import Pell.Main3LargeAnalyticPointwiseBlock
import Pell.Main3LargeAnalyticElementaryActiveKeyAggregate
import Pell.Main3LargeAnalyticElementaryComplexActiveKeyCoarseGeometry
import Pell.Main3LargeAnalyticElementaryRealActiveKeyCoarseGeometry
import Mathlib.Tactic

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticElementaryPointwiseBlock_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Unconditional elementary-sieve analogue of the production pointwise
large-analytic interface. -/
def Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimateElementary : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ c : ℝ, 0 < c →
      10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ∀ h : ℤ, ∀ v D N : ℕ,
          (h, v, D, N) ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
          ((squarefreeShiftedSquareBlock
            (shiftedSquareA h v) D Y N).card : ℝ) ≤
            K * theta ^ 12 *
              (1 + Real.log
                (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ))) ^ 6 *
              (main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
                (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)))

/-- The key-summed real/complex cell estimates give the precise pointwise
block interface consumed by the reviewed outer absorption theorem. -/
theorem main3LargeAnalytic_thetaTwelveLogSixPointwiseBlockEstimate_elementary :
    Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimateElementary := by
  obtain ⟨Csum, hCsum, hkeyWeight⟩ :=
    exists_pos_sum_surfaceLevelDivisors_add_one_blockAuxiliaryKeyGate_le_shiftWeight_fiveEighths_workspace
  let K : ℝ := main3LargeAnalyticCoarseKeyTotalConstant * Csum
  have hK : 0 < K := by
    dsimp only [K, main3LargeAnalyticCoarseKeyTotalConstant]
    positivity
  refine ⟨K, hK, ?_⟩
  intro c hc hsmall
  have hpositive :=
    eventually_main3LargeAnalytic_positiveShift_block_cast_le_sum_ite_complexEnvelopes_elementary
      c hc hsmall
  have hnegative :=
    eventually_main3LargeAnalytic_negativeShift_block_cast_le_sum_ite_realEnvelopes_elementary
      c hc hsmall
  have hscale :=
    eventually_main3LargeAnalytic_uniformSieveScale_package c hc hsmall 0
  filter_upwards [hpositive, hnegative, hscale, eventually_ge_atTop 65536] with
      Y hpositiveY hnegativeY hscaleY hY
  intro theta htheta hadmissible h v D N hi
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let gate := main3LargeAnalytic_blockAuxiliaryKeyGate h v
  let y : ℝ := Y
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let S : ℝ := 1 + Real.log (2 * W * y)
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Q : ℝ := y ^ (1 - s)
  let weight : ShiftedSquareAuxiliaryKey → ℝ := fun key ↦
    ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) + 1
  have hscalePackage := hscaleY theta htheta hadmissible
  have hSieve : 4 ≤ main3LargeAnalyticSieveN theta Y :=
    hscalePackage.2.1
  have ha0 : shiftedSquareA h v ≠ 0 :=
    main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have habsOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha0
  have hWone : (1 : ℝ) ≤ W := by
    dsimp only [W, main3LargeAnalyticShiftWeight]
    nlinarith
  have hWpos : 0 < W := zero_lt_one.trans_le hWone
  have hyOne : (1 : ℝ) ≤ y := by
    dsimp only [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hargOne : (1 : ℝ) ≤ 2 * W * y := by
    nlinarith [mul_le_mul hWone hyOne (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ W)]
  have hSone : (1 : ℝ) ≤ S := by
    dsimp only [S]
    exact le_add_of_nonneg_right (Real.log_nonneg hargOne)
  have hQpos : 0 < Q := by
    dsimp only [Q, y]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hweightSum : (∑ key ∈ gate, weight key) ≤
      Csum * W ^ ((5 : ℝ) / 8) := by
    simpa only [gate, weight, W] using hkeyWeight theta Y h v D N hi
  rcases lt_or_gt_of_ne ha0 with haNeg | haPos
  · let cost : ShiftedSquareAuxiliaryKey → ℝ := fun key ↦
      let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
      let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
      let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
      let Delta := Real.sqrt
        |(NumberField.discr
          (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
      let Mmesh := (main3UnbalancedM theta Y : ℝ)
      let Kbranch := (2 * E / Mmesh) / Delta
      let Lbranch := Kbranch / 2 + 5
      let Lscale := (annularDyadicScaleCount Fscale : ℝ)
      let H₀ := 144 * Real.sqrt E
      let reciprocalBudget :=
        38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀) *
            (1 + Real.log (2 * Lbranch)) +
          201553920000 * Lscale * Real.sqrt (E * Mmesh / Delta)
      let baseCost :=
        2048 * (main3BalancedDegree theta : ℝ) * theta *
            ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
          4
      if I.Nonempty then
        (36 * Mmesh * Lscale) * baseCost +
          2 * fullCellElementarySieveVariableAggregateEnvelope
            (main3LargeAnalyticSieveN theta Y)
            (2 * main3BalancedDegree theta + 1)
            (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
            reciprocalBudget
      else 0
    have hblock :
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) ≤
          ∑ key ∈ gate, cost key := by
      simpa only [gate, cost] using
        hnegativeY theta htheta hadmissible hY hi haNeg
    have hpoint : ∀ key ∈ gate,
        cost key ≤
          main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
            weight key * (Real.sqrt W * Q) := by
      intro key hkey
      have hcoarse :=
        main3LargeAnalytic_realActiveKeyElementaryEnvelope_le_coarse_workspace
          htheta hY hi (by simpa only [gate] using hkey) haNeg hSieve
      simpa only [cost, weight, S, W, Q, y, s] using hcoarse
    have hsum := sum_coarseKeyTargets_le_nineEighths_workspace
      gate cost weight main3LargeAnalyticCoarseKeyTotalConstant Csum
      theta S W Q
      (by unfold main3LargeAnalyticCoarseKeyTotalConstant; positivity)
      hCsum.le htheta hSone hWpos hQpos.le hpoint hweightSum
    exact hblock.trans (by simpa only [K, S, W, Q, y, s] using hsum)
  · let cost : ShiftedSquareAuxiliaryKey → ℝ := fun key ↦
      let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
      let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
      let Delta := Real.sqrt
        |(NumberField.discr
          (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
      let Mmesh := (main3UnbalancedM theta Y : ℝ)
      let Kbranch := (6 * E / Mmesh) / Delta
      let Lbranch := Kbranch / 2 + 2
      let H₀ := 2 * Real.sqrt E
      let reciprocalBudget :=
        9216 * Real.sqrt E * (2 + Real.log H₀) *
            (1 + Real.log (2 * Lbranch)) +
          663552 * Real.sqrt (E * Mmesh / Delta)
      let baseCost :=
        2048 * (main3BalancedDegree theta : ℝ) * theta *
            ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
          4
      if I.Nonempty then
        (10 * Mmesh) * baseCost +
          2 * fullCellElementarySieveVariableAggregateEnvelope
            (main3LargeAnalyticSieveN theta Y)
            (2 * main3BalancedDegree theta + 1)
            (10 * Mmesh) (3 * E / (Mmesh * Delta)) reciprocalBudget
      else 0
    have hblock :
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) ≤
          ∑ key ∈ gate, cost key := by
      simpa only [gate, cost] using
        hpositiveY theta htheta hadmissible hY hi haPos
    have hpoint : ∀ key ∈ gate,
        cost key ≤
          main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
            weight key * (Real.sqrt W * Q) := by
      intro key hkey
      have hcoarse :=
        main3LargeAnalytic_complexActiveKeyEnvelope_le_coarse_elementary
          htheta hY hi (by simpa only [gate] using hkey) haPos hSieve
      simpa only [cost, weight, S, W, Q, y, s] using hcoarse
    have hsum := sum_coarseKeyTargets_le_nineEighths_workspace
      gate cost weight main3LargeAnalyticCoarseKeyTotalConstant Csum
      theta S W Q
      (by unfold main3LargeAnalyticCoarseKeyTotalConstant; positivity)
      hCsum.le htheta hSone hWpos hQpos.le hpoint hweightSum
    exact hblock.trans (by simpa only [K, S, W, Q, y, s] using hsum)


end

end PellPaper

#print axioms PellPaper.main3LargeAnalytic_thetaTwelveLogSixPointwiseBlockEstimate_elementary

