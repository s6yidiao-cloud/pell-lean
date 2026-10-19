import Pell.Main3LargeAnalyticRealActiveKeyCoarseGeometry
import Pell.Main3LargeAnalyticElementarySieveEnvelope
import Mathlib.Tactic

/-!
# Elementary coarse geometry for one negative-shift Main3 key

The accepted real-cell geometry is unchanged.  The only new power budget is
the elementary envelope's mesh term `cellCount * Z^3`.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

local instance main3LargeAnalyticElementaryRealActiveKeyCoarseGeometry_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- One nonempty real active-key envelope is bounded by the common coarse key
target.  The empty case is retained literally by the `if`. -/
theorem main3LargeAnalytic_realActiveKeyElementaryEnvelope_le_coarse_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (_ha : shiftedSquareA h v < 0)
    (hSieve : 4 ≤ main3LargeAnalyticSieveN theta Y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
    let y : ℝ := Y
    let W := main3LargeAnalyticShiftWeight h v
    let S := 1 + Real.log (2 * W * y)
    let s := 1 / (32 * theta ^ 2)
    let Q := y ^ (1 - s)
    let T := Real.sqrt W * Q
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let M : ℝ := main3UnbalancedM theta Y
    let K := (2 * E / M) / Delta
    let Lbranch := K / 2 + 5
    let Lscale := (annularDyadicScaleCount
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) : ℝ)
    let H₀ := 144 * Real.sqrt E
    let reciprocalBudget :=
      38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀) *
          (1 + Real.log (2 * Lbranch)) +
        201553920000 * Lscale * Real.sqrt (E * M / Delta)
    let baseCost :=
      2048 * (main3BalancedDegree theta : ℝ) * theta *
          ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
        4
    (if I.Nonempty then
      (36 * M * Lscale) * baseCost +
        2 * fullCellElementarySieveVariableAggregateEnvelope
          (main3LargeAnalyticSieveN theta Y)
          (2 * main3BalancedDegree theta + 1)
          (36 * M * Lscale) (4 * E / (M * Delta)) reciprocalBudget
    else 0) ≤
      main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
        (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) + 1) *
        T := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
  let y : ℝ := Y
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let S : ℝ := 1 + Real.log (2 * W * y)
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Z : ℝ := y ^ s
  let Q : ℝ := y ^ (1 - s)
  let T : ℝ := Real.sqrt W * Q
  let E : ℝ := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta : ℝ := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let M : ℝ := main3UnbalancedM theta Y
  let K : ℝ := (2 * E / M) / Delta
  let Lbranch : ℝ := K / 2 + 5
  let Lscale : ℝ := annularDyadicScaleCount
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
  let H₀ : ℝ := 144 * Real.sqrt E
  let reciprocalBudget : ℝ :=
    38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀) *
        (1 + Real.log (2 * Lbranch)) +
      201553920000 * Lscale * Real.sqrt (E * M / Delta)
  let baseCost : ℝ :=
    2048 * (main3BalancedDegree theta : ℝ) * theta *
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
      4
  let tau : ℝ :=
    ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ)
  let Lp : ℝ := 7 * (1 + Real.log (2 * y))
  let degree : ℕ := 2 * main3BalancedDegree theta + 1
  have hYtwo : 2 ≤ Y := by omega
  have hcommon := main3LargeAnalytic_activeKey_commonCoarseBounds_workspace
    htheta hYtwo hi hkey
  dsimp only at hcommon
  obtain ⟨hSone, hsqrtWone, hT0, hLp, hdegree, hMpos, hZpos,
    hEpos, hDeltaPos, hZsqrtE, hsqrtE, hZsqrtEMD, hsqrtEMD,
    hratioZ, hLscale⟩ := hcommon
  have hthetaOne : 1 ≤ theta := by linarith
  have hQpos : 0 < Q := by
    dsimp only [Q, y]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hQT : Q ≤ T := by
    dsimp only [T]
    have := mul_le_mul_of_nonneg_right hsqrtWone hQpos.le
    nlinarith
  have hpowers :=
    main3LargeAnalytic_outer_mesh_sieve_power_package_workspace
      theta Y htheta hYtwo
  have hMpower : M ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using hpowers.1
  have hMZcube : M * Z ^ 3 ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using
      main3LargeAnalytic_outer_mesh_sieve_cube_le_workspace
        theta Y htheta hYtwo
  have hlogs := main3LargeAnalytic_activeKey_outerLogBounds_workspace
    htheta hYtwo hi hkey
  have hlogH : 2 + Real.log H₀ ≤ 16 * S := by
    simpa only [S, W, y, E, Delta, M, K, Lbranch, H₀] using
      hlogs.2.2.2.1
  have hlogL : 1 + Real.log (2 * Lbranch) ≤ 16 * S := by
    simpa only [S, W, y, E, Delta, M, K, Lbranch, H₀] using
      hlogs.2.2.2.2
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hlogL0 : 0 ≤ 1 + Real.log (2 * Lbranch) := by
    have harg : (1 : ℝ) ≤ 2 * Lbranch := by
      dsimp only [Lbranch]
      nlinarith
    exact add_nonneg zero_le_one (Real.log_nonneg harg)
  have hLscale0 : 0 ≤ Lscale := by
    dsimp only [Lscale]
    positivity
  have hreciprocalZ : Z * reciprocalBudget ≤
      3000000000000000 * S ^ 3 * T := by
    simpa only [reciprocalBudget] using
      realReciprocalBudget_mul_le_common_workspace
        Z Lscale (Real.sqrt E) (Real.sqrt (E * M / Delta))
        (2 + Real.log H₀) (1 + Real.log (2 * Lbranch)) S T
        hZpos.le hLscale0 (Real.sqrt_nonneg E) (Real.sqrt_nonneg _)
        hSone hT0 hLscale hlogL0 hlogH hlogL hZsqrtE hZsqrtEMD
  have hreciprocalOne : reciprocalBudget ≤
      3000000000000000 * S ^ 3 * T := by
    have h := realReciprocalBudget_mul_le_common_workspace
      1 Lscale (Real.sqrt E) (Real.sqrt (E * M / Delta))
      (2 + Real.log H₀) (1 + Real.log (2 * Lbranch)) S T
      (by norm_num) hLscale0 (Real.sqrt_nonneg E) (Real.sqrt_nonneg _)
      hSone hT0 hLscale hlogL0 hlogH hlogL
      (by simpa only [one_mul] using hsqrtE)
      (by simpa only [one_mul] using hsqrtEMD)
    change 1 * reciprocalBudget ≤ 3000000000000000 * S ^ 3 * T at h
    simpa only [one_mul] using h
  let reciprocalPlus : ℝ := max 0 reciprocalBudget
  have hreciprocalPlus0 : 0 ≤ reciprocalPlus := by
    dsimp only [reciprocalPlus]
    exact le_max_left _ _
  have hreciprocalPlus : reciprocalPlus ≤
      3000000000000000 * S ^ 3 * T := by
    dsimp only [reciprocalPlus]
    exact max_le (by positivity) hreciprocalOne
  have hZreciprocalPlus : Z * reciprocalPlus ≤
      3000000000000000 * S ^ 3 * T := by
    by_cases hr : 0 ≤ reciprocalBudget
    · simpa only [reciprocalPlus, max_eq_right hr] using hreciprocalZ
    · have hr' : reciprocalBudget ≤ 0 := le_of_not_ge hr
      simp only [reciprocalPlus, max_eq_left hr', mul_zero]
      positivity
  have hcellCount : 0 ≤ 36 * M * Lscale := by positivity
  have harea : 0 ≤ 4 * E / (M * Delta) := by positivity
  have hLp0 : 0 ≤ Lp := by
    dsimp only [Lp]
    have hyOne : (1 : ℝ) ≤ y := by
      dsimp only [y]
      exact_mod_cast (show 1 ≤ Y by omega)
    have harg : (1 : ℝ) ≤ 2 * y := by nlinarith
    exact mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (Real.log_nonneg harg))
  have hcellArea :
      (36 * M * Lscale) * (4 * E / (M * Delta)) / Z ≤
        31363200 * S * T := by
    have hidentity :
        (36 * M * Lscale) * (4 * E / (M * Delta)) / Z =
          144 * Lscale * ((E / Delta) / Z) := by
      calc
        (36 * M * Lscale) * (4 * E / (M * Delta)) / Z =
            144 * Lscale * (M / M) * ((E / Delta) / Z) := by ring
        _ = 144 * Lscale * ((E / Delta) / Z) := by
          rw [div_self hMpos.ne']
          ring
    rw [hidentity]
    calc
      144 * Lscale * ((E / Delta) / Z) ≤
          144 * (100 * S) * (2178 * T) := by gcongr
      _ = 31363200 * S * T := by ring
  have hcellZ : (36 * M * Lscale) * Z ^ 3 ≤ 7200 * S * T := by
    calc
      (36 * M * Lscale) * Z ^ 3 = 36 * Lscale * (M * Z ^ 3) := by ring
      _ ≤ 36 * (100 * S) * (2 * Q) := by gcongr
      _ = 7200 * S * Q := by ring
      _ ≤ 7200 * S * T := by gcongr
  have hvariableMax :=
    fullCellElementarySieveVariableAggregateEnvelope_le_max_reciprocal
      (main3LargeAnalyticSieveN theta Y) degree
      (36 * M * Lscale) (4 * E / (M * Delta)) reciprocalBudget hSieve
  have hvariablePower :=
    main3LargeAnalytic_fullCellElementaryVariableAggregate_le_powerAggregate
      theta Y degree (36 * M * Lscale) (4 * E / (M * Delta)) reciprocalPlus
      htheta hYtwo hSieve hcellCount harea hreciprocalPlus0
  have hvariable :
      fullCellElementarySieveVariableAggregateEnvelope
          (main3LargeAnalyticSieveN theta Y) degree
          (36 * M * Lscale) (4 * E / (M * Delta)) reciprocalBudget ≤
        fullCellElementarySievePowerAggregateEnvelope
          Z Lp degree (36 * M * Lscale) (4 * E / (M * Delta)) reciprocalPlus := by
    exact hvariableMax.trans (by
      simpa only [Z, Lp, y, s] using hvariablePower)
  have hpowerCoarse :=
    fullCellElementarySievePowerAggregateEnvelope_le_coarseKeyEnvelope
      theta S T (36 * M * Lscale) (4 * E / (M * Delta)) Z Lp reciprocalPlus degree
      hthetaOne hSone hT0 hcellCount harea hZpos hLp0
      hreciprocalPlus0 hLp hdegree hcellArea hcellZ
      hZreciprocalPlus hreciprocalPlus
  have hB : (main3BalancedDegree theta : ℝ) ≤ theta ^ 3 := by
    linarith [main3BalancedDegree_add_one_le_theta_cube theta htheta]
  have hBtheta : (main3BalancedDegree theta : ℝ) * theta ≤ theta ^ 4 := by
    calc
      (main3BalancedDegree theta : ℝ) * theta ≤ theta ^ 3 * theta := by gcongr
      _ = theta ^ 4 := by ring
  have hthetaFourSix : theta ^ 4 ≤ theta ^ 6 :=
    pow_le_pow_right₀ hthetaOne (by omega)
  have htau0 : 0 ≤ tau := by dsimp only [tau]; positivity
  have hbaseCost : baseCost ≤ 2052 * theta ^ 6 * (tau + 1) := by
    dsimp only [baseCost]
    have hmain :
        2048 * (main3BalancedDegree theta : ℝ) * theta * tau ≤
          2048 * theta ^ 6 * (tau + 1) := by
      calc
        2048 * (main3BalancedDegree theta : ℝ) * theta * tau =
            (2048 * ((main3BalancedDegree theta : ℝ) * theta)) * tau := by ring
        _ ≤ (2048 * theta ^ 4) * tau := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hBtheta (by norm_num)) htau0
        _ ≤ (2048 * theta ^ 6) * tau := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hthetaFourSix (by norm_num)) htau0
        _ ≤ 2048 * theta ^ 6 * (tau + 1) := by
          have htau : tau ≤ tau + 1 := by linarith
          exact mul_le_mul_of_nonneg_left htau (by positivity)
    have hfour : (4 : ℝ) ≤ 4 * theta ^ 6 * (tau + 1) := by
      have hthetaSix : 1 ≤ theta ^ 6 := one_le_pow₀ hthetaOne
      have htauOne : 1 ≤ tau + 1 := by linarith
      nlinarith [mul_le_mul hthetaSix htauOne (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ theta ^ 6)]
    nlinarith
  have hcell : 36 * M * Lscale ≤ 7200 * S * T := by
    calc
      36 * M * Lscale = 36 * Lscale * M := by ring
      _ ≤ 36 * (100 * S) * (2 * Q) := by gcongr
      _ = 7200 * S * Q := by ring
      _ ≤ 7200 * S * T := by gcongr
  have hbase : (36 * M * Lscale) * baseCost ≤
      14774400 * theta ^ 6 * S ^ 4 * (tau + 1) * T := by
    have hSfour : S ≤ S ^ 4 := by
      have hraw : S ^ (1 : ℕ) ≤ S ^ (4 : ℕ) :=
        pow_le_pow_right₀ hSone (by norm_num)
      simpa using hraw
    calc
      (36 * M * Lscale) * baseCost ≤
          (7200 * S * T) * (2052 * theta ^ 6 * (tau + 1)) := by gcongr
      _ = 14774400 * theta ^ 6 * S * (tau + 1) * T := by ring
      _ ≤ 14774400 * theta ^ 6 * S ^ 4 * (tau + 1) * T := by gcongr
  have htarget0 :
      0 ≤ main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
        (tau + 1) * T := by
    unfold main3LargeAnalyticCoarseKeyTotalConstant
    positivity
  change
    (if I.Nonempty then
      (36 * M * Lscale) * baseCost +
        2 * fullCellElementarySieveVariableAggregateEnvelope
          (main3LargeAnalyticSieveN theta Y) degree
          (36 * M * Lscale) (4 * E / (M * Delta)) reciprocalBudget
    else 0) ≤
      main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
        (tau + 1) * T
  by_cases hI : I.Nonempty
  · rw [if_pos hI]
    calc
      _ ≤ (36 * M * Lscale) * baseCost +
          2 * fullCellElementarySievePowerAggregateEnvelope
            Z Lp degree (36 * M * Lscale) (4 * E / (M * Delta))
              reciprocalPlus := by
        gcongr
      _ ≤ 14774400 * theta ^ 6 * S ^ 4 * (tau + 1) * T +
          main3LargeAnalyticCoarseKeyEnvelopeConstant * theta ^ 6 * S ^ 4 * T :=
        add_le_add hbase hpowerCoarse
      _ ≤ main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
          (tau + 1) * T := by
        unfold main3LargeAnalyticCoarseKeyEnvelopeConstant
        unfold main3LargeAnalyticCoarseKeyTotalConstant
        have htauOne : 1 ≤ tau + 1 := by linarith
        have hmono : theta ^ 6 * S ^ 4 * T ≤
            theta ^ 6 * S ^ 4 * (tau + 1) * T := by
          calc
            theta ^ 6 * S ^ 4 * T =
                1 * (theta ^ 6 * S ^ 4 * T) := by ring
            _ ≤ (tau + 1) * (theta ^ 6 * S ^ 4 * T) :=
              mul_le_mul_of_nonneg_right htauOne (by positivity)
            _ = theta ^ 6 * S ^ 4 * (tau + 1) * T := by ring
        have hpowerLift :
            1000000000000000000000 * theta ^ 6 * S ^ 4 * T ≤
              1000000000000000000000 * theta ^ 6 * S ^ 4 *
                (tau + 1) * T := by
          calc
            1000000000000000000000 * theta ^ 6 * S ^ 4 * T =
                1000000000000000000000 * (theta ^ 6 * S ^ 4 * T) := by ring
            _ ≤ 1000000000000000000000 *
                (theta ^ 6 * S ^ 4 * (tau + 1) * T) :=
              mul_le_mul_of_nonneg_left hmono (by norm_num)
            _ = 1000000000000000000000 * theta ^ 6 * S ^ 4 *
                (tau + 1) * T := by ring
        have hP0 : 0 ≤ theta ^ 6 * S ^ 4 * (tau + 1) * T := by
          positivity
        calc
          14774400 * theta ^ 6 * S ^ 4 * (tau + 1) * T +
                1000000000000000000000 * theta ^ 6 * S ^ 4 * T ≤
              14774400 * theta ^ 6 * S ^ 4 * (tau + 1) * T +
                1000000000000000000000 * theta ^ 6 * S ^ 4 *
                  (tau + 1) * T := add_le_add_right hpowerLift _
          _ = (1000000000000000000000 + 14774400) *
                (theta ^ 6 * S ^ 4 * (tau + 1) * T) := by ring
          _ ≤ 2000000000000000000000 *
                (theta ^ 6 * S ^ 4 * (tau + 1) * T) := by
            exact mul_le_mul_of_nonneg_right (by norm_num) hP0
          _ = 2000000000000000000000 * theta ^ 6 * S ^ 4 *
                (tau + 1) * T := by ring
  · rw [if_neg hI]
    exact htarget0


end

end PellPaper

#print axioms PellPaper.main3LargeAnalytic_realActiveKeyElementaryEnvelope_le_coarse_workspace

