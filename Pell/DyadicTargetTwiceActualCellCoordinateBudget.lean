import Pell.DyadicBalancedCoordinateBudget
import Pell.DyadicBalancedScaleConsequences
import Pell.DyadicFactorBoxNormalization
import Mathlib.Tactic

/-!
# Coordinate budgets from an actual target-twice factor cell

The split-exponent balanced route must not use the source-clearing exponent
to control residual-coordinate sizes.  An actual nonempty factor cell already
supplies the sharper geometric normalization
`DE * sqrt Y <= (2Y)^cellTheta`.  Together with
`cellTheta <= 2 * theta`, this gives the source-coordinate budget directly.

The same cell supplies `UV < 2Y`; the wide prime threshold then bounds the
positive denominator by `UV`.  Thus all three coordinate logarithms needed
by the residual square sieve follow without any upper bound on the clearing
exponent.
-/

namespace PellPaper

noncomputable section

/-- The source-coordinate logarithm is controlled by actual-cell height,
independently of either determinant decay or source-clearing exponents. -/
theorem log_dyadicSourceCoordinateBound_le_two_mul_theta_logBudget_of_nonemptyFactorCell
    (cellTheta theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ)
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcellTheta : cellTheta ≤ 2 * theta) :
    Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
      2 * theta * (1 + Real.log (2 * (Y : ℝ))) := by
  let DE : ℝ :=
    ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)
  let Z : ℝ := 2 * (Y : ℝ)
  have hnormalization :=
    nonempty_dyadicFactorBoxCell_endpoint_normalization hcell
  have hheight : DE * Real.sqrt (Y : ℝ) ≤ Z ^ cellTheta := by
    simpa only [DE, Z, Nat.cast_mul, Nat.cast_ofNat] using hnormalization.2.2
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ Y by omega)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Y : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hYone
  have hDE0 : 0 ≤ DE := by dsimp [DE]; positivity
  have hDEheight : DE ≤ Z ^ cellTheta := by
    calc
      DE = DE * 1 := by ring
      _ ≤ DE * Real.sqrt (Y : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtOne hDE0
      _ ≤ Z ^ cellTheta := hheight
  have hsourceUpper : (dyadicSourceCoordinateBound i : ℝ) ≤
      2 * Z ^ cellTheta := by
    calc
      (dyadicSourceCoordinateBound i : ℝ) ≤ 2 * DE := by
        simpa only [DE] using
          dyadicSourceCoordinateBound_le_two_mul_endpointProduct i
      _ ≤ 2 * Z ^ cellTheta := by gcongr
  have hsourcePos : (0 : ℝ) < dyadicSourceCoordinateBound i := by
    exact_mod_cast dyadicSourceCoordinateBound_pos i
  have hlogUpper :
      Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
        Real.log (2 * Z ^ cellTheta) :=
    Real.log_le_log hsourcePos hsourceUpper
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hlogIdentity : Real.log (2 * Z ^ cellTheta) =
      Real.log 2 + cellTheta * Real.log Z := by
    rw [Real.log_mul (by norm_num)
        (Real.rpow_pos_of_pos hZpos cellTheta).ne',
      Real.log_rpow hZpos]
  have hlogZ0 : 0 ≤ Real.log Z := by
    apply Real.log_nonneg
    dsimp [Z]
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htheta0 : 0 ≤ theta := by linarith
  calc
    Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
        Real.log 2 + cellTheta * Real.log Z := by
      simpa only [hlogIdentity] using hlogUpper
    _ ≤ 1 + (2 * theta) * Real.log Z := by
      gcongr
    _ ≤ 2 * theta * (1 + Real.log Z) := by
      nlinarith
    _ = 2 * theta * (1 + Real.log (2 * (Y : ℝ))) := by
      rfl

/-- A nonempty actual factor cell and the wide natural-scale prime threshold
discharge the complete residual square-sieve budget.  In particular, no
upper or sign hypothesis on a source-clearing exponent appears. -/
theorem fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale_of_nonemptyFactorCell
    (B : ℕ) (cellTheta theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (hM : 0 < M) (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcellTheta : cellTheta ≤ 2 * theta)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hprime :
      1280000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
        dyadicBalancedSquareSieveRealScale i M) :
    fullCellResidualSieveUniformBudgetThreshold i M B
        (dyadicSourceTargetCellResidualHeight B i) ≤
      (dyadicBalancedSquareSieveScale i M : ℝ) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  let A4 : ℝ := 1 + Real.log (2 * ((2 * Y : ℕ) : ℝ))
  have hnormalization :=
    nonempty_dyadicFactorBoxCell_endpoint_normalization hcell
  have hUV : U * V ≤ ((2 * Y : ℕ) : ℝ) := by
    have hUVlt : U * V < 2 * (Y : ℝ) := by
      simpa only [U, V] using hnormalization.1
    norm_num at hUVlt ⊢
    exact hUVlt.le
  have hwide :=
    widePrimeThreshold_two_le_balancedScale_and_denominator_le_targetProduct
      theta Y i M hM htheta hY hprime
  have hMUV : (M : ℝ) ≤ U * V := by
    simpa only [U, V] using hwide.2
  have hMtwoYReal : (M : ℝ) ≤ ((2 * Y : ℕ) : ℝ) := hMUV.trans hUV
  have hMtwoY : M ≤ 2 * Y := by exact_mod_cast hMtwoYReal
  have hauxY : 2 ≤ 2 * Y := by omega
  have hsource : Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
      2 * theta * A := by
    simpa only [A] using
      log_dyadicSourceCoordinateBound_le_two_mul_theta_logBudget_of_nonemptyFactorCell
        cellTheta theta Y i hcell htheta hY hcellTheta
  have htarget0 : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤ A4 := by
    simpa only [A4, U, V] using
      log_dyadicTargetCoordinateBound_le_logBudget (2 * Y) i hUV
  have hdenominator0 : Real.log ((M : ℝ) + 1) ≤ A4 := by
    simpa only [A4] using
      log_dyadicCellDenominator_add_one_le_logBudget (2 * Y) M hauxY hMtwoY
  have htwoYone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Real.log_nonneg htwoYone)
  have htwoYpos : (0 : ℝ) < 2 * (Y : ℝ) := by positivity
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hA4upper : A4 ≤ 2 * A := by
    dsimp [A4, A]
    rw [show (2 : ℝ) * ((2 * Y : ℕ) : ℝ) =
        2 * (2 * (Y : ℝ)) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) htwoYpos.ne']
    linarith [Real.log_nonneg htwoYone]
  have htarget : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤
      2 * A := htarget0.trans hA4upper
  have hdenominator : Real.log ((M : ℝ) + 1) ≤
      2 * theta * A := by
    calc
      Real.log ((M : ℝ) + 1) ≤ A4 := hdenominator0
      _ ≤ 2 * A := hA4upper
      _ ≤ 2 * theta * A := by
        have hthetaOne : (1 : ℝ) ≤ theta := by linarith
        nlinarith [zero_le_one.trans hAone]
  have hprime' :
      640000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
        dyadicBalancedSquareSieveRealScale i M := by
    calc
      640000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
          1280000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) := by
        have htheta0 : 0 ≤ theta := by linarith
        have hfactor0 : 0 ≤
            theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) := by
          exact mul_nonneg (pow_nonneg htheta0 7)
            (by simpa only [A] using zero_le_one.trans hAone)
        nlinarith
      _ ≤ dyadicBalancedSquareSieveRealScale i M := hprime
  have hthreshold :=
    fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale_of_primeThreshold
      B theta 2 Y i M htheta (by norm_num) hY hBupper
      (by simpa only [A] using hsource)
      (by simpa only [A] using htarget)
      (by simpa only [A] using hdenominator)
      (by simpa only [show (320000 : ℝ) * 2 = 640000 by norm_num]
        using hprime')
  exact hthreshold

end

end PellPaper
