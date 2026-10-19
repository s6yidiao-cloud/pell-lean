import Pell.Main3AuxKeyWeightedSum
import Pell.Main3LargeAnalyticUniformSieveScale
import Pell.Main3LargeAnalyticActiveKeySieveAggregate
import Pell.Main3LargeAnalyticActiveKeyCoarseGeometry
import Pell.Main3LargeAnalyticRealActiveKeyCoarseGeometry
import Pell.Main3LargeAnalyticOuterAbsorption
import Mathlib.Tactic

/-!
# Workspace: key-summed pointwise Main3 large-analytic block bound

This file combines the active-key cell envelopes with the two deliberately
coarse auxiliary-key sums needed for the final `9/8` shift exponent.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticPointwiseBlock_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- At epsilon `1/8`, the unweighted key count and the surface-level divisor
weight have the same `W^(5/8)` envelope. -/
theorem exists_pos_sum_surfaceLevelDivisors_add_one_blockAuxiliaryKeyGate_le_shiftWeight_fiveEighths_workspace :
    ∃ Csum : ℝ, 0 < Csum ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
          ((((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ) + 1)) ≤
          Csum * main3LargeAnalyticShiftWeight h v ^ ((5 : ℝ) / 8) := by
  obtain ⟨Cone, hCone, hone⟩ :=
    exists_pos_sum_one_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
      ((1 : ℝ) / 8) (by norm_num)
  obtain ⟨Cdiv, hCdiv, hdiv⟩ :=
    exists_pos_sum_surfaceLevelDivisors_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
      ((1 : ℝ) / 8) (by norm_num)
  refine ⟨Cdiv + Cone, add_pos hCdiv hCone, ?_⟩
  intro theta Y h v D N hi
  have hdiv' := hdiv theta Y h v D N hi
  have hone' := hone theta Y h v D N hi
  have hexponent : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
  rw [hexponent] at hdiv' hone'
  calc
    (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        ((((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ) + 1)) =
      (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ)) +
      ∑ _key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v, (1 : ℝ) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ Cdiv * main3LargeAnalyticShiftWeight h v ^ ((5 : ℝ) / 8) +
        Cone * main3LargeAnalyticShiftWeight h v ^ ((5 : ℝ) / 8) :=
      add_le_add hdiv' hone'
    _ = (Cdiv + Cone) *
        main3LargeAnalyticShiftWeight h v ^ ((5 : ℝ) / 8) := by ring

/-- Scalar summation ledger: a `W^(5/8)` key weight multiplied by the
geometric `sqrt W` in every cell envelope is exactly `W^(9/8)`. -/
theorem sum_coarseKeyTargets_le_nineEighths_workspace
    {α : Type*} (gate : Finset α) (cost : α → ℝ)
    (weight : α → ℝ)
    (K₀ Csum theta S W Q : ℝ)
    (hK₀ : 0 ≤ K₀) (hCsum : 0 ≤ Csum)
    (htheta : 3 ≤ theta) (hS : 1 ≤ S)
    (hW : 0 < W) (hQ : 0 ≤ Q)
    (hpoint : ∀ key ∈ gate,
      cost key ≤ K₀ * theta ^ 6 * S ^ 4 * weight key *
        (Real.sqrt W * Q))
    (hweight : (∑ key ∈ gate, weight key) ≤
      Csum * W ^ ((5 : ℝ) / 8)) :
    (∑ key ∈ gate, cost key) ≤
      (K₀ * Csum) * theta ^ 12 * S ^ 6 *
        (W ^ ((9 : ℝ) / 8) * Q) := by
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have hthetaSixTwelve : theta ^ 6 ≤ theta ^ 12 :=
    pow_le_pow_right₀ hthetaOne (by omega)
  have hSfourSix : S ^ 4 ≤ S ^ 6 :=
    pow_le_pow_right₀ hS (by omega)
  have hsqrtW : Real.sqrt W * W ^ ((5 : ℝ) / 8) =
      W ^ ((9 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hW]
    congr 1
    norm_num
  have hfactor0 : 0 ≤ K₀ * theta ^ 6 * S ^ 4 *
      (Real.sqrt W * Q) := by positivity
  calc
    (∑ key ∈ gate, cost key) ≤
        ∑ key ∈ gate,
          K₀ * theta ^ 6 * S ^ 4 * weight key *
            (Real.sqrt W * Q) :=
      Finset.sum_le_sum fun key hkey => hpoint key hkey
    _ = (K₀ * theta ^ 6 * S ^ 4 * (Real.sqrt W * Q)) *
        (∑ key ∈ gate, weight key) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key hkey
      ring
    _ ≤ (K₀ * theta ^ 6 * S ^ 4 * (Real.sqrt W * Q)) *
        (Csum * W ^ ((5 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left hweight hfactor0
    _ = (K₀ * Csum) * theta ^ 6 * S ^ 4 *
        (W ^ ((9 : ℝ) / 8) * Q) := by rw [← hsqrtW]; ring
    _ ≤ (K₀ * Csum) * theta ^ 12 * S ^ 6 *
        (W ^ ((9 : ℝ) / 8) * Q) := by gcongr

/-- The key-summed real/complex cell estimates give the precise pointwise
block interface consumed by the reviewed outer absorption theorem. -/
theorem main3LargeAnalytic_thetaTwelveLogSixPointwiseBlockEstimate_workspace :
    Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimate := by
  intro hWeil
  obtain ⟨Csum, hCsum, hkeyWeight⟩ :=
    exists_pos_sum_surfaceLevelDivisors_add_one_blockAuxiliaryKeyGate_le_shiftWeight_fiveEighths_workspace
  let K : ℝ := main3LargeAnalyticCoarseKeyTotalConstant * Csum
  have hK : 0 < K := by
    dsimp only [K, main3LargeAnalyticCoarseKeyTotalConstant]
    positivity
  refine ⟨K, hK, ?_⟩
  intro c hc hsmall
  have hpositive :=
    eventually_main3LargeAnalytic_positiveShift_block_cast_le_sum_ite_complexEnvelopes
      hWeil c hc hsmall
  have hnegative :=
    eventually_main3LargeAnalytic_negativeShift_block_cast_le_sum_ite_realEnvelopes
      hWeil c hc hsmall
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
          2 * fullCellOddDegreeSieveVariableAggregateEnvelope
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
        main3LargeAnalytic_realActiveKeyEnvelope_le_coarse_workspace
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
          2 * fullCellOddDegreeSieveVariableAggregateEnvelope
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
        main3LargeAnalytic_complexActiveKeyEnvelope_le_coarse_workspace
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

#print axioms PellPaper.exists_pos_sum_surfaceLevelDivisors_add_one_blockAuxiliaryKeyGate_le_shiftWeight_fiveEighths_workspace
#print axioms PellPaper.sum_coarseKeyTargets_le_nineEighths_workspace
#print axioms PellPaper.main3LargeAnalytic_thetaTwelveLogSixPointwiseBlockEstimate_workspace
