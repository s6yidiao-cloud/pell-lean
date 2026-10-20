import Pell.Main3BalancedCeilingParameters
import Pell.DyadicSplitExponentParameterAdapter
import Pell.TwoLayerTargetTwiceSplitExponentFanRate
import Mathlib.Tactic

/-!
# Main3 parameters on a nonempty high-factor dyadic box

This module combines the canonical main3 ceiling parameters with the frozen
split-exponent endpoint adapter.  On a nonempty actual factor cell, the
high-`DE` alternative and the main3 growth hypothesis force the literal
target endpoint scale `X = E^2 V` above `1536 Y`.  That strengthened lower
bound simultaneously supplies the local determinant threshold, `M <= X`,
and the otherwise missing comparison `m <= qDecay`.

The second endpoint comparison and the same growth hypothesis give
`X <= Y^(2 theta)`.  The final theorem collects every non-prime, non-`N0`
premise of the split-exponent target-twice balanced local-box theorem after
the literal main3 substitutions.
-/

namespace PellPaper

noncomputable section

/-- In the high-`DE` alternative, actual-cell comparability upgrades the
target endpoint scale to the strengthened lower bound `1536 Y < X`. -/
theorem nonempty_dyadicFactorBoxCell_highDE_main3_targetScale_lower
    (theta cellTheta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hhighDE :
      (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) :
    1536 * (Y : ℝ) < dyadicTargetEndpointScale i := by
  let y : ℝ := Y
  let DE : ℝ :=
    ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)
  let X : ℝ := dyadicTargetEndpointScale i
  let delta : ℝ := 1 / (100 * theta ^ 2)
  let c : ℝ := 1 / 2 - delta
  have hthetaSq : (9 : ℝ) ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hthetaSqPos : 0 < theta ^ 2 := lt_of_lt_of_le (by norm_num) hthetaSq
  have hyPos : 0 < y := by dsimp [y]; positivity
  have hlogYpos : 0 < Real.log y := by
    apply Real.log_pos
    dsimp [y]
    exact_mod_cast (show 1 < Y by omega)
  have hlogGrowth : 800 * theta ^ 2 < Real.log y := by
    have hlog := Real.strictMonoOn_log (Real.exp_pos _) hyPos hYgrow
    rw [Real.log_exp] at hlog
    simpa only [y] using hlog
  have hlogThirty : (30 : ℝ) < Real.log y := by nlinarith
  have hdeltaUpper : delta ≤ 1 / 6 := by
    have hdenom : 0 < 100 * theta ^ 2 := by positivity
    dsimp [delta]
    apply (div_le_iff₀ hdenom).2
    nlinarith
  have hcLower : (1 / 3 : ℝ) ≤ c := by
    dsimp [c]
    linarith
  have hten : (10 : ℝ) < c * Real.log y := by
    calc
      (10 : ℝ) < (1 / 3 : ℝ) * Real.log y := by nlinarith
      _ ≤ c * Real.log y :=
        mul_le_mul_of_nonneg_right hcLower hlogYpos.le
  have hlogConstant : Real.log (15360 : ℝ) < c * Real.log y :=
    log_15360_lt_ten.trans hten
  have hconstantPower : (15360 : ℝ) < y ^ c := by
    rw [Real.rpow_def_of_pos hyPos]
    calc
      (15360 : ℝ) = Real.exp (Real.log (15360 : ℝ)) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 15360)]
      _ < Real.exp (c * Real.log y) := Real.exp_lt_exp.mpr hlogConstant
      _ = Real.exp (Real.log y * c) := by rw [mul_comm]
  have hDE : y ^ (1 - delta) < DE := by
    simpa only [y, delta, DE] using hhighDE
  have hsqrtPos : 0 < Real.sqrt y := Real.sqrt_pos.2 hyPos
  have hheight : DE * Real.sqrt y ≤ 10 * X := by
    simpa only [y, DE, X] using
      (nonempty_dyadicFactorBoxCell_endpointHeight_targetScale_comparable
        hcell).1
  have hexponent : c + 1 = (1 - delta) + 1 / 2 := by
    dsimp [c]
    ring
  have hscaled : (15360 : ℝ) * y < 10 * X := by
    calc
      (15360 : ℝ) * y < y ^ c * y :=
        mul_lt_mul_of_pos_right hconstantPower hyPos
      _ = y ^ (c + 1) := by
        rw [Real.rpow_add hyPos, Real.rpow_one]
      _ = y ^ ((1 - delta) + 1 / 2) := by rw [hexponent]
      _ = y ^ (1 - delta) * Real.sqrt y := by
        rw [Real.rpow_add hyPos, Real.sqrt_eq_rpow]
      _ < DE * Real.sqrt y := mul_lt_mul_of_pos_right hDE hsqrtPos
      _ ≤ 10 * X := hheight
  dsimp [y, X] at hscaled ⊢
  nlinarith

/-- The upper actual-cell comparison and the main3 growth hypothesis absorb
all fixed constants and place the target scale below `Y^(2 theta)`. -/
theorem nonempty_dyadicFactorBoxCell_main3_targetScale_le_rpow
    (theta cellTheta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (hcellTheta : cellTheta = theta + 1 / 4)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    dyadicTargetEndpointScale i ≤ (Y : ℝ) ^ (2 * theta) := by
  subst cellTheta
  let y : ℝ := Y
  let X : ℝ := dyadicTargetEndpointScale i
  let Z : ℝ := 2 * y
  let a : ℝ := theta + 1 / 4
  let b : ℝ := 2 * theta
  have hthetaSq : (9 : ℝ) ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hyPos : 0 < y := by dsimp [y]; positivity
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hlogYpos : 0 < Real.log y := by
    apply Real.log_pos
    dsimp [y]
    exact_mod_cast (show 1 < Y by omega)
  have hlogGrowth : 800 * theta ^ 2 < Real.log y := by
    have hlog := Real.strictMonoOn_log (Real.exp_pos _) hyPos hYgrow
    rw [Real.log_exp] at hlog
    simpa only [y] using hlog
  have hXupper : X ≤ 7 * Z ^ a := by
    simpa only [X, Z, y, a, Nat.cast_mul, Nat.cast_ofNat] using
      dyadicTargetEndpointScale_le_seven_mul_twoY_rpow_of_nonemptyFactorCell
        hcell
  have hlogSeven : Real.log (7 : ℝ) ≤ 2 := by
    have hlt : Real.log (7 : ℝ) < 2 :=
      (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)).2 (by
        calc
          (7 : ℝ) < (2.7 : ℝ) ^ 2 := by norm_num
          _ < (Real.exp 1) ^ 2 := by
            gcongr
            exact (by norm_num : (2.7 : ℝ) < 2.7182818283).trans
              Real.exp_one_gt_d9
          _ = Real.exp 2 := by
            rw [← Real.exp_nat_mul]
            norm_num)
    exact hlt.le
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hfixed : theta + 9 / 4 ≤ (theta - 1 / 4) * Real.log y := by
    have hpoly : theta + 9 / 4 ≤ 200 * theta ^ 2 := by
      nlinarith [sq_nonneg (theta - 3)]
    have hquarterGrowth : 200 * theta ^ 2 < (1 / 4 : ℝ) * Real.log y := by
      nlinarith
    have hquarter : (1 / 4 : ℝ) ≤ theta - 1 / 4 := by linarith
    have hquarterLog : (1 / 4 : ℝ) * Real.log y ≤
        (theta - 1 / 4) * Real.log y :=
      mul_le_mul_of_nonneg_right hquarter hlogYpos.le
    exact hpoly.trans (hquarterGrowth.le.trans hquarterLog)
  have hlogZ : Real.log Z = Real.log 2 + Real.log y := by
    dsimp [Z]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne']
  have hlogBudget :
      Real.log (7 * Z ^ a) ≤ Real.log (y ^ b) := by
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
        (Real.rpow_pos_of_pos hZpos a).ne',
      Real.log_rpow hZpos, Real.log_rpow hyPos, hlogZ]
    dsimp [a, b]
    calc
      Real.log 7 + (theta + 1 / 4) *
          (Real.log 2 + Real.log y) ≤
          2 + (theta + 1 / 4) * (1 + Real.log y) := by
        gcongr
      _ = (theta + 1 / 4) * Real.log y + (theta + 9 / 4) := by ring
      _ ≤ (theta + 1 / 4) * Real.log y +
          (theta - 1 / 4) * Real.log y := by gcongr
      _ = 2 * theta * Real.log y := by ring
  have hpower : 7 * Z ^ a ≤ y ^ b := by
    have hleftPos : 0 < 7 * Z ^ a := by positivity
    have hrightPos : 0 < y ^ b := Real.rpow_pos_of_pos hyPos b
    calc
      7 * Z ^ a = Real.exp (Real.log (7 * Z ^ a)) := by
        rw [Real.exp_log hleftPos]
      _ ≤ Real.exp (Real.log (y ^ b)) := Real.exp_le_exp.mpr hlogBudget
      _ = y ^ b := Real.exp_log hrightPos
  exact hXupper.trans (by simpa only [y, X, b] using hpower)

/-- The strengthened lower scale places the ceiling mesh below `X` and the
exact ceiling exponent below the determinant-decay exponent. -/
theorem nonempty_dyadicFactorBoxCell_highDE_main3_mesh_le_targetScale_and_decay
    (theta cellTheta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hhighDE :
      (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) :
    let X := dyadicTargetEndpointScale i
    let M := main3BalancedM theta Y
    let m := main3BalancedMLogExponent theta Y
    (M : ℝ) ≤ X ∧ m ≤ dyadicSplitExponentDecay Y X := by
  let y : ℝ := Y
  let X : ℝ := dyadicTargetEndpointScale i
  let M : ℕ := main3BalancedM theta Y
  let m : ℝ := main3BalancedMLogExponent theta Y
  have hmesh := main3BalancedM_parameter_package theta Y htheta hY
  have hMpos : 0 < M := by simpa only [M] using hmesh.1
  have hMleY : M ≤ Y := by simpa only [M] using hmesh.2.1
  have hmLog : m * Real.log y = Real.log (M : ℝ) := by
    simpa only [m, M, y] using hmesh.2.2.2.2.2
  have hlower : 1536 * y < X := by
    simpa only [y, X] using
      nonempty_dyadicFactorBoxCell_highDE_main3_targetScale_lower
        theta cellTheta Y i htheta hY hcell hYgrow hhighDE
  have hyOne : (1 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hXthreshold : 1536 ≤ X := by
    calc
      (1536 : ℝ) = 1536 * 1 := by ring
      _ ≤ 1536 * y := mul_le_mul_of_nonneg_left hyOne (by norm_num)
      _ ≤ X := hlower.le
  have hMrealLeY : (M : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast hMleY
  have hMX : (M : ℝ) ≤ X := by
    calc
      (M : ℝ) ≤ y := hMrealLeY
      _ ≤ 1536 * y := by nlinarith [show 0 ≤ y from hyOne.trans' (by norm_num)]
      _ ≤ X := hlower.le
  have hscaledM : (1536 : ℝ) * (M : ℝ) ≤ X := by
    calc
      (1536 : ℝ) * (M : ℝ) ≤ 1536 * y :=
        mul_le_mul_of_nonneg_left hMrealLeY (by norm_num)
      _ ≤ X := hlower.le
  have hMrealPos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hlogScaled :
      Real.log (1536 * (M : ℝ)) ≤ Real.log X := by
    exact Real.log_le_log (by positivity) hscaledM
  have hlogM : Real.log (M : ℝ) ≤ Real.log X - Real.log 1536 := by
    rw [Real.log_mul (by norm_num : (1536 : ℝ) ≠ 0) hMrealPos.ne'] at hlogScaled
    linarith
  have hlogYpos : 0 < Real.log y := by
    apply Real.log_pos
    dsimp [y]
    exact_mod_cast (show 1 < Y by omega)
  have hlogYne : Real.log (Y : ℝ) ≠ 0 := by
    simpa only [y] using hlogYpos.ne'
  have hmDecay : m ≤ dyadicSplitExponentDecay Y X := by
    have hmul : m * Real.log y ≤
        dyadicSplitExponentDecay Y X * Real.log y := by
      calc
        m * Real.log y = Real.log (M : ℝ) := hmLog
        _ ≤ Real.log X - Real.log 1536 := hlogM
        _ = dyadicSplitExponentDecay Y X * Real.log y := by
          rw [dyadicSplitExponentDecay]
          dsimp only [y]
          exact (div_mul_cancel₀ _ hlogYne).symm
    nlinarith
  dsimp only
  exact ⟨hMX, hmDecay⟩

/-- Complete main3 high-box parameter package.  Its conjunctions occur in
the same order as all non-prime, non-`N0` hypotheses of
`eventually_dyadicFactorBoxCell_card_le_targetTwiceSplitExponentBalancedBox`
after setting

`B = ceil(theta^2)`, `H0 = 2(B+1)`, `Q = theta`,
`cellTheta = theta+1/4`, `X = E^2 V`, and using the literal main3 mesh.
-/
theorem main3BalancedHighBox_parameters
    (theta cellTheta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcellTheta : cellTheta = theta + 1 / 4)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (hhighDE :
      (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) :
    let B := main3BalancedDegree theta
    let H0 := 2 * (B + 1)
    let Q := theta
    let X := dyadicTargetEndpointScale i
    let M := main3BalancedM theta Y
    let m := main3BalancedMLogExponent theta Y
    let qDecay := dyadicSplitExponentDecay Y X
    let qCost := dyadicSplitExponentCost Y X
    let sigma := dyadicSplitExponentSigma X
    0 < M ∧ 2 ≤ Y ∧ 2 ≤ Q ∧
      3 ≤ theta ∧ cellTheta ≤ 2 * theta ∧
      theta ^ 2 ≤ (B : ℝ) ∧ (B : ℝ) < theta ^ 2 + 1 ∧
      9 / 10 ≤ m ∧ m ≤ 1 ∧
      m ≤ qDecay ∧ qDecay ≤ 7 * theta / 6 ∧
      (1 - m) * theta ^ 2 ≤ 1 / 50 ∧
      Real.exp (800 * theta ^ 2) < (Y : ℝ) ∧
      (M : ℝ) ≤ X ∧ X ≤ (Y : ℝ) ^ (2 * Q) ∧
      X ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
        ((2 ^ i.2.2.2 : ℕ) : ℝ) ∧
      1536 ≤ X ∧ 0 < sigma ∧
      Real.exp (Real.log (1536 : ℝ) / sigma) ≤ X ∧
      m * Real.log (Y : ℝ) ≤ Real.log (M : ℝ) ∧
      qDecay * Real.log (Y : ℝ) =
        (1 - sigma) * Real.log X ∧
      (qCost - qDecay) * Real.log (Y : ℝ) ≤ Real.log 15360 ∧
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        (Y : ℝ) ^ (qCost - 1 / 2) ∧
      H0 = 2 * (B + 1) := by
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let Q : ℝ := theta
  let X : ℝ := dyadicTargetEndpointScale i
  let M : ℕ := main3BalancedM theta Y
  let m : ℝ := main3BalancedMLogExponent theta Y
  let qDecay : ℝ := dyadicSplitExponentDecay Y X
  let qCost : ℝ := dyadicSplitExponentCost Y X
  let sigma : ℝ := dyadicSplitExponentSigma X
  have hdegree := main3BalancedDegree_nearSquare theta
  have hmesh := main3BalancedM_parameter_package theta Y htheta hY
  have hlower : 1536 * (Y : ℝ) < X := by
    simpa only [X] using
      nonempty_dyadicFactorBoxCell_highDE_main3_targetScale_lower
        theta cellTheta Y i htheta hY hcell hYgrow hhighDE
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ Y by omega)
  have hXthreshold : 1536 ≤ X := by
    calc
      (1536 : ℝ) = 1536 * 1 := by ring
      _ ≤ 1536 * (Y : ℝ) :=
        mul_le_mul_of_nonneg_left hYone (by norm_num)
      _ ≤ X := hlower.le
  have hmeshTarget :=
    nonempty_dyadicFactorBoxCell_highDE_main3_mesh_le_targetScale_and_decay
      theta cellTheta Y i htheta hY hcell hYgrow hhighDE
  have hMX : (M : ℝ) ≤ X := by
    simpa only [M, X] using hmeshTarget.1
  have hmqDecay : m ≤ qDecay := by
    simpa only [m, qDecay, X] using hmeshTarget.2
  have hXupper : X ≤ (Y : ℝ) ^ (2 * Q) := by
    simpa only [X, Q] using
      nonempty_dyadicFactorBoxCell_main3_targetScale_le_rpow
        theta cellTheta Y i htheta hY hcell hcellTheta hYgrow
  have hsplit :=
    nonempty_dyadicFactorBoxCell_splitExponent_parameter_package
      hcell htheta hY hcellTheta (by simpa only [X] using hXthreshold) hYgrow
  have hcellThetaUpper : cellTheta ≤ 2 * theta := by
    rw [hcellTheta]
    linarith
  dsimp only
  refine ⟨by simpa only [M] using hmesh.1, hY, by simpa only [Q] using
      (show (2 : ℝ) ≤ theta by linarith), htheta, hcellThetaUpper,
    by simpa only [B] using hdegree.1,
    by simpa only [B] using hdegree.2,
    by simpa only [m] using hmesh.2.2.1,
    by simpa only [m] using hmesh.2.2.2.1,
    hmqDecay,
    by simpa only [qDecay, X] using hsplit.2.2.2.2.2,
    by simpa only [m] using hmesh.2.2.2.2.1,
    hYgrow, hMX, hXupper, ?_, hXthreshold,
    by simpa only [sigma, X] using hsplit.1,
    by simpa only [sigma, X] using hsplit.2.1,
    by simpa only [m, M] using hmesh.2.2.2.2.2.le,
    by simpa only [qDecay, sigma, X] using hsplit.2.2.1,
    by simpa only [qCost, qDecay, X] using hsplit.2.2.2.1,
    by simpa only [qCost, X] using hsplit.2.2.2.2.1, rfl⟩
  · rfl

end

end PellPaper
