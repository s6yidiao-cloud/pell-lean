import Pell.Main3LargeAnalyticOuterParameterBounds
import Pell.Main3LargeAnalyticOuterLogBounds
import Pell.Main3LargeAnalyticOuterPowerLedger
import Pell.Main3LargeAnalyticCoarseKeyEnvelope
import Pell.Main3LargeAnalyticActiveKeySieveAggregate
import Pell.Main3BalancedHighPolynomialAbsorption
import Mathlib.Tactic

/-!
# Workspace: coarse geometry for one active Main3 auxiliary key

This file substitutes the actual Main3 parameters into the reviewed
power-form sieve envelope.  The deliberately coarse common target is

`sqrt(A_a) * Y^(1 - 1/(32*theta^2))`.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

local instance main3LargeAnalyticActiveKeyCoarseGeometry_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Common absolute constant after adding the elementary base-cost term to
the power-form sieve envelope. -/
def main3LargeAnalyticCoarseKeyTotalConstant : ℝ :=
  2000000000000000000000

/-- Common scale bounds used by both the real and complex active-key
envelopes. -/
theorem main3LargeAnalytic_activeKey_commonCoarseBounds_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let y : ℝ := Y
    let W := main3LargeAnalyticShiftWeight h v
    let S := 1 + Real.log (2 * W * y)
    let s := 1 / (32 * theta ^ 2)
    let Z := y ^ s
    let M : ℝ := main3UnbalancedM theta Y
    let Q := y ^ (1 - s)
    let T := Real.sqrt W * Q
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Lp := 7 * (1 + Real.log (2 * y))
    let degree := 2 * main3BalancedDegree theta + 1
    let Lscale := (annularDyadicScaleCount
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) : ℝ)
    1 ≤ S ∧
      1 ≤ Real.sqrt W ∧
      0 ≤ T ∧
      Lp ≤ 7 * S ∧
      (degree : ℝ) + 1 ≤ 2 * theta ^ 3 ∧
      0 < M ∧ 0 < Z ∧ 0 < E ∧ 0 < Delta ∧
      Z * Real.sqrt E ≤ 33 * T ∧
      Real.sqrt E ≤ 33 * T ∧
      Z * Real.sqrt (E * M / Delta) ≤ 94 * T ∧
      Real.sqrt (E * M / Delta) ≤ 94 * T ∧
      (E / Delta) / Z ≤ 2178 * T ∧
      Lscale ≤ 100 * S := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let y : ℝ := Y
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let S : ℝ := 1 + Real.log (2 * W * y)
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Z : ℝ := y ^ s
  let M : ℝ := main3UnbalancedM theta Y
  let Q : ℝ := y ^ (1 - s)
  let T : ℝ := Real.sqrt W * Q
  let E : ℝ := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta : ℝ := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Lp : ℝ := 7 * (1 + Real.log (2 * y))
  let degree : ℕ := 2 * main3BalancedDegree theta + 1
  let Lscale : ℝ := annularDyadicScaleCount
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
  have ha0 := main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have habsOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha0
  have hWtwo : 2 ≤ W := by
    dsimp only [W, main3LargeAnalyticShiftWeight]
    nlinarith
  have hWone : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := zero_le_one.trans hWone
  have hsqrtWone : 1 ≤ Real.sqrt W := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hWone
  have hypos : 0 < y := by dsimp only [y]; positivity
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact Real.rpow_pos_of_pos hypos _
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hlogs := main3LargeAnalytic_activeKey_outerLogBounds_workspace
    htheta hY hi hkey
  have hS : 1 ≤ S := by
    simpa only [S, W, y] using hlogs.1
  have hLyS : 1 + Real.log (2 * y) ≤ S := by
    have harg : 2 * y ≤ 2 * W * y := by
      have hy0 : 0 ≤ y := hypos.le
      nlinarith [mul_le_mul_of_nonneg_right hWone hy0]
    have hlog := Real.log_le_log (by positivity : 0 < 2 * y) harg
    dsimp only [S]
    linarith
  have hLp : Lp ≤ 7 * S := by
    dsimp only [Lp]
    gcongr
  have hdegree : (degree : ℝ) + 1 ≤ 2 * theta ^ 3 := by
    have hB := main3BalancedDegree_add_one_le_theta_cube theta htheta
    dsimp only [degree]
    push_cast
    linarith
  have hMpos : 0 < M := by
    dsimp only [M]
    exact_mod_cast (main3UnbalancedM_parameter_package theta Y htheta hY).1
  have hZpos : 0 < Z := by
    dsimp only [Z]
    exact Real.rpow_pos_of_pos hypos _
  have hEpos : 0 < E := by
    simpa only [E] using
      (main3LargeAnalyticFixedKeyTargetScaleUpper_le_ceiling_workspace
        (Y := Y) (h := h) (v := v) (by omega : 0 < Y) hkey).1
  have hsqrtAbsPos : 0 < Real.sqrt |(shiftedSquareA h v : ℝ)| := by
    exact Real.sqrt_pos.2 (abs_pos.mpr (by exact_mod_cast ha0))
  have hsqrtAbsDelta : Real.sqrt |(shiftedSquareA h v : ℝ)| ≤ Delta := by
    simpa only [Delta] using
      main3LargeAnalytic_sqrt_abs_shift_le_sqrt_fieldDiscriminant_workspace hi
  have hDeltaPos : 0 < Delta := hsqrtAbsPos.trans_le hsqrtAbsDelta
  have hpowers :=
    main3LargeAnalytic_outer_mesh_sieve_power_package_workspace
      theta Y htheta hY
  have hMpower : M ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using hpowers.1
  have hMZpower : M * Z ^ 2 ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.1
  have hyZpower : y / Z ≤ Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.2.1
  have hZsqrtYM : Z * Real.sqrt (y * M) ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.2.2.1
  have hsqrtYM : Real.sqrt (y * M) ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.2.2.2.1
  have hZsqrtY : Z * Real.sqrt y ≤ Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.2.2.2.2.1
  have hsqrtY : Real.sqrt y ≤ Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.2.2.2.2.2
  have hsqrtEraw : Real.sqrt E ≤ 33 * Real.sqrt (y * W) := by
    simpa only [E, y, W] using
      main3LargeAnalytic_sqrt_targetScale_le_workspace
        (by omega : 0 < Y) hi hkey
  have hsqrtYW : Real.sqrt (y * W) = Real.sqrt y * Real.sqrt W := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ y)]
  have hZsqrtE : Z * Real.sqrt E ≤ 33 * T := by
    calc
      Z * Real.sqrt E ≤ Z * (33 * Real.sqrt (y * W)) := by gcongr
      _ = 33 * Real.sqrt W * (Z * Real.sqrt y) := by
        rw [hsqrtYW]
        ring
      _ ≤ 33 * Real.sqrt W * Q := by gcongr
      _ = 33 * T := by dsimp only [T]; ring
  have hsqrtE : Real.sqrt E ≤ 33 * T := by
    calc
      Real.sqrt E ≤ 33 * Real.sqrt (y * W) := hsqrtEraw
      _ = 33 * Real.sqrt W * Real.sqrt y := by rw [hsqrtYW]; ring
      _ ≤ 33 * Real.sqrt W * Q := by gcongr
      _ = 33 * T := by dsimp only [T]; ring
  have hsqrtEMDraw : Real.sqrt (E * M / Delta) ≤
      47 * Real.sqrt (y * M) * W ^ ((1 : ℝ) / 4) := by
    simpa only [E, M, Delta, y, W] using
      main3LargeAnalytic_sqrt_targetScale_mul_mesh_div_discriminant_le_workspace
        (by omega : 0 < Y) hi hkey
  have hWquarter : W ^ ((1 : ℝ) / 4) ≤ Real.sqrt W := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hWone (by norm_num)
  have hZsqrtEMD : Z * Real.sqrt (E * M / Delta) ≤ 94 * T := by
    calc
      Z * Real.sqrt (E * M / Delta) ≤
          Z * (47 * Real.sqrt (y * M) * W ^ ((1 : ℝ) / 4)) := by
        gcongr
      _ = 47 * (Z * Real.sqrt (y * M)) * W ^ ((1 : ℝ) / 4) := by ring
      _ ≤ 47 * (2 * Q) * Real.sqrt W := by gcongr
      _ = 94 * T := by dsimp only [T]; ring
  have hsqrtEMD : Real.sqrt (E * M / Delta) ≤ 94 * T := by
    calc
      Real.sqrt (E * M / Delta) ≤
          47 * Real.sqrt (y * M) * W ^ ((1 : ℝ) / 4) := hsqrtEMDraw
      _ ≤ 47 * (2 * Q) * Real.sqrt W := by gcongr
      _ = 94 * T := by dsimp only [T]; ring
  have hratioRaw : E / Delta ≤
      2178 * y * Real.sqrt |(shiftedSquareA h v : ℝ)| := by
    simpa only [E, Delta, y] using
      main3LargeAnalytic_targetScale_div_discriminant_le_workspace
        (by omega : 0 < Y) hi hkey
  have hsqrtAbsW : Real.sqrt |(shiftedSquareA h v : ℝ)| ≤ Real.sqrt W := by
    apply Real.sqrt_le_sqrt
    dsimp only [W, main3LargeAnalyticShiftWeight]
    nlinarith [abs_nonneg (shiftedSquareA h v : ℝ)]
  have hratioZ : (E / Delta) / Z ≤ 2178 * T := by
    calc
      (E / Delta) / Z ≤
          (2178 * y * Real.sqrt |(shiftedSquareA h v : ℝ)|) / Z := by
        gcongr
      _ ≤ (2178 * y * Real.sqrt W) / Z := by gcongr
      _ = 2178 * Real.sqrt W * (y / Z) := by ring
      _ ≤ 2178 * Real.sqrt W * Q := by gcongr
      _ = 2178 * T := by dsimp only [T]; ring
  have hLscale : Lscale ≤ 100 * S := by
    simpa only [Lscale, S, W, y] using
      main3LargeAnalytic_annularDyadicScaleCount_cast_le_workspace hY hi
  exact ⟨hS, hsqrtWone, hT0, hLp, hdegree, hMpos, hZpos,
    hEpos, hDeltaPos, hZsqrtE, hsqrtE, hZsqrtEMD, hsqrtEMD,
    hratioZ, hLscale⟩

/-- One nonempty complex active-key envelope is bounded by the common coarse
key target.  The empty case is retained literally by the `if`. -/
theorem main3LargeAnalytic_complexActiveKeyEnvelope_le_coarse_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (_ha : 0 < shiftedSquareA h v)
    (hSieve : 4 ≤ main3LargeAnalyticSieveN theta Y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
    let K := (6 * E / M) / Delta
    let Lbranch := K / 2 + 2
    let H₀ := 2 * Real.sqrt E
    let reciprocalBudget :=
      9216 * Real.sqrt E * (2 + Real.log H₀) *
          (1 + Real.log (2 * Lbranch)) +
        663552 * Real.sqrt (E * M / Delta)
    let baseCost :=
      2048 * (main3BalancedDegree theta : ℝ) * theta *
          ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
        4
    (if I.Nonempty then
      (10 * M) * baseCost +
        2 * fullCellOddDegreeSieveVariableAggregateEnvelope
          (main3LargeAnalyticSieveN theta Y)
          (2 * main3BalancedDegree theta + 1)
          (10 * M) (3 * E / (M * Delta)) reciprocalBudget
    else 0) ≤
      main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
        (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) + 1) *
        T := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
  let K : ℝ := (6 * E / M) / Delta
  let Lbranch : ℝ := K / 2 + 2
  let H₀ : ℝ := 2 * Real.sqrt E
  let reciprocalBudget : ℝ :=
    9216 * Real.sqrt E * (2 + Real.log H₀) *
        (1 + Real.log (2 * Lbranch)) +
      663552 * Real.sqrt (E * M / Delta)
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
    hratioZ, _hLscale⟩ := hcommon
  have hthetaOne : 1 ≤ theta := by linarith
  have htheta0 : 0 ≤ theta := zero_le_one.trans hthetaOne
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
  have hMZpower : M * Z ^ 2 ≤ 2 * Q := by
    simpa only [y, s, Z, M, Q] using hpowers.2.1
  have hlogs := main3LargeAnalytic_activeKey_outerLogBounds_workspace
    htheta hYtwo hi hkey
  have hlogH : 2 + Real.log H₀ ≤ 16 * S := by
    simpa only [S, W, y, E, Delta, M, K, Lbranch, H₀] using hlogs.2.1
  have hlogL : 1 + Real.log (2 * Lbranch) ≤ 16 * S := by
    simpa only [S, W, y, E, Delta, M, K, Lbranch, H₀] using hlogs.2.2.1
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hlogL0 : 0 ≤ 1 + Real.log (2 * Lbranch) := by
    have harg : (1 : ℝ) ≤ 2 * Lbranch := by
      dsimp only [Lbranch]
      nlinarith
    exact add_nonneg zero_le_one (Real.log_nonneg harg)
  have hreciprocalZ : Z * reciprocalBudget ≤
      3000000000000000 * S ^ 3 * T := by
    simpa only [reciprocalBudget] using
      complexReciprocalBudget_mul_le_common_workspace
        Z (Real.sqrt E) (Real.sqrt (E * M / Delta))
        (2 + Real.log H₀) (1 + Real.log (2 * Lbranch)) S T
        hZpos.le (Real.sqrt_nonneg E) (Real.sqrt_nonneg _)
        hSone hT0 hlogL0 hlogH hlogL hZsqrtE hZsqrtEMD
  have hreciprocalOne : reciprocalBudget ≤
      3000000000000000 * S ^ 3 * T := by
    have h := complexReciprocalBudget_mul_le_common_workspace
      1 (Real.sqrt E) (Real.sqrt (E * M / Delta))
      (2 + Real.log H₀) (1 + Real.log (2 * Lbranch)) S T
      (by norm_num) (Real.sqrt_nonneg E) (Real.sqrt_nonneg _)
      hSone hT0 hlogL0 hlogH hlogL
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
  have hcellCount : 0 ≤ 10 * M := by positivity
  have harea : 0 ≤ 3 * E / (M * Delta) := by positivity
  have hLp0 : 0 ≤ Lp := by
    dsimp only [Lp]
    have hyOne : (1 : ℝ) ≤ y := by
      dsimp only [y]
      exact_mod_cast (show 1 ≤ Y by omega)
    have harg : (1 : ℝ) ≤ 2 * y := by nlinarith
    exact mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (Real.log_nonneg harg))
  have hcellArea :
      (10 * M) * (3 * E / (M * Delta)) / Z ≤
        31363200 * S * T := by
    have hidentity :
        (10 * M) * (3 * E / (M * Delta)) / Z =
          30 * ((E / Delta) / Z) := by
      calc
        (10 * M) * (3 * E / (M * Delta)) / Z =
            30 * (M / M) * ((E / Delta) / Z) := by ring
        _ = 30 * ((E / Delta) / Z) := by rw [div_self hMpos.ne']; ring
    rw [hidentity]
    calc
      30 * ((E / Delta) / Z) ≤ 30 * (2178 * T) := by gcongr
      _ ≤ 31363200 * S * T := by
        have hST : T ≤ S * T := by
          have := mul_le_mul_of_nonneg_right hSone hT0
          nlinarith
        nlinarith
  have hcellZ : (10 * M) * Z ^ 2 ≤ 7200 * S * T := by
    calc
      (10 * M) * Z ^ 2 = 10 * (M * Z ^ 2) := by ring
      _ ≤ 10 * (2 * Q) := by gcongr
      _ = 20 * Q := by ring
      _ ≤ 20 * T := by gcongr
      _ ≤ 20 * (S * T) := by
        gcongr
        nlinarith
      _ ≤ 7200 * S * T := by
        have hST0 : 0 ≤ S * T := mul_nonneg (by linarith) hT0
        have := mul_le_mul_of_nonneg_right
          (by norm_num : (20 : ℝ) ≤ 7200) hST0
        nlinarith
  have hvariableMax :=
    fullCellOddDegreeSieveVariableAggregateEnvelope_le_max_reciprocal_workspace
      (main3LargeAnalyticSieveN theta Y) degree
      (10 * M) (3 * E / (M * Delta)) reciprocalBudget hSieve
  have hvariablePower :=
    main3LargeAnalytic_fullCellVariableAggregate_le_powerAggregate
      theta Y degree (10 * M) (3 * E / (M * Delta)) reciprocalPlus
      htheta hYtwo hSieve hcellCount harea hreciprocalPlus0
  have hvariable :
      fullCellOddDegreeSieveVariableAggregateEnvelope
          (main3LargeAnalyticSieveN theta Y) degree
          (10 * M) (3 * E / (M * Delta)) reciprocalBudget ≤
        fullCellOddDegreeSievePowerAggregateEnvelope
          Z Lp degree (10 * M) (3 * E / (M * Delta)) reciprocalPlus := by
    exact hvariableMax.trans (by
      simpa only [Z, Lp, y, s] using hvariablePower)
  have hpowerCoarse :=
    fullCellOddDegreeSievePowerAggregateEnvelope_le_coarseKeyEnvelope_workspace
      theta S T (10 * M) (3 * E / (M * Delta)) Z Lp reciprocalPlus degree
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
  have hcell : 10 * M ≤ 7200 * S * T := by
    calc
      10 * M ≤ 10 * (2 * Q) := by gcongr
      _ = 20 * Q := by ring
      _ ≤ 20 * T := by gcongr
      _ ≤ 20 * (S * T) := by
        gcongr
        nlinarith
      _ ≤ 7200 * S * T := by
        have hST0 : 0 ≤ S * T := mul_nonneg (by linarith) hT0
        have := mul_le_mul_of_nonneg_right
          (by norm_num : (20 : ℝ) ≤ 7200) hST0
        nlinarith
  have hbase : (10 * M) * baseCost ≤
      14774400 * theta ^ 6 * S ^ 4 * (tau + 1) * T := by
    have hSfour : S ≤ S ^ 4 := by
      have hraw : S ^ (1 : ℕ) ≤ S ^ (4 : ℕ) :=
        pow_le_pow_right₀ hSone (by norm_num)
      simpa using hraw
    calc
      (10 * M) * baseCost ≤
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
      (10 * M) * baseCost +
        2 * fullCellOddDegreeSieveVariableAggregateEnvelope
          (main3LargeAnalyticSieveN theta Y) degree
          (10 * M) (3 * E / (M * Delta)) reciprocalBudget
    else 0) ≤
      main3LargeAnalyticCoarseKeyTotalConstant * theta ^ 6 * S ^ 4 *
        (tau + 1) * T
  by_cases hI : I.Nonempty
  · rw [if_pos hI]
    calc
      _ ≤ (10 * M) * baseCost +
          2 * fullCellOddDegreeSievePowerAggregateEnvelope
            Z Lp degree (10 * M) (3 * E / (M * Delta)) reciprocalPlus := by
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

#print axioms PellPaper.main3LargeAnalytic_activeKey_commonCoarseBounds_workspace
#print axioms PellPaper.main3LargeAnalytic_complexActiveKeyEnvelope_le_coarse_workspace
