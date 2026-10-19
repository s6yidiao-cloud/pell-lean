import Pell.Main3BalancedCeilingParameters
import Pell.DyadicFactorBoxNormalization
import Pell.DyadicBalancedSquareSieveScale
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The natural balanced square-sieve scale in main3

For the main3 ceiling

`M = ceil (Y^(1 - 1/(50 theta^2)))`,

a nonempty dyadic factor cell has enough target mass for its real square-sieve
scale to dominate `Y^(1/(400 theta^2))`.  The proof retains the literal
dyadic loss `Y < 4UV` and the ceiling loss `M <= 2Y^a`.  The fixed growth
hypothesis supplies the remaining factor eight.

This is a project-specific parameter calculation; no analytic estimate is
introduced here.
-/

namespace PellPaper

noncomputable section

/-- On every nonempty actual factor cell, the main3 localization mesh leaves
at least the fourth-root power saving required by the balanced square sieve. -/
theorem nonempty_dyadicFactorBoxCell_main3Balanced_rpow_le_squareSieveRealScale
    (theta cellTheta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty) :
    (Y : ℝ) ^ (1 / (400 * theta ^ 2)) ≤
      dyadicBalancedSquareSieveRealScale i (main3BalancedM theta Y) := by
  let y : ℝ := Y
  let a : ℝ := main3BalancedMExponent theta
  let delta : ℝ := 1 / (100 * theta ^ 2)
  let M : ℕ := main3BalancedM theta Y
  let P : ℝ :=
    ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hthetaSqPos : 0 < theta ^ 2 := by positivity
  have hyOne : (1 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hyPos : 0 < y := zero_lt_one.trans_le hyOne
  have haBounds := main3BalancedMExponent_mem htheta
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact (by norm_num : (0 : ℝ) ≤ 9 / 10).trans haBounds.1
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hMpos : 0 < M := by
    have hpackage := main3BalancedM_parameter_package theta Y htheta hY
    simpa only [M] using hpackage.1
  have hMrealPos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hyaOne : (1 : ℝ) ≤ y ^ a := Real.one_le_rpow hyOne ha0
  have hMceil : (M : ℝ) < y ^ a + 1 := by
    dsimp [M, main3BalancedM, y, a]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg Y) _)
  have hMupper : (M : ℝ) ≤ 2 * y ^ a := by
    exact hMceil.le.trans (by nlinarith)
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hyLtFourP : y < 4 * P := by
    simpa only [y, P] using
      (nonempty_dyadicFactorBoxCell_endpoint_normalization hcell).2.1
  have hlogGrowth : 800 * theta ^ 2 < Real.log y := by
    have hlog := Real.strictMonoOn_log (Real.exp_pos _) hyPos hYgrow
    rw [Real.log_exp] at hlog
    simpa only [y] using hlog
  have hdeltaLog : 8 < Real.log y * delta := by
    have hdenom : 0 < 100 * theta ^ 2 := by positivity
    calc
      (8 : ℝ) = (800 * theta ^ 2) / (100 * theta ^ 2) := by
        field_simp [hthetaSqPos.ne']
        norm_num
      _ < Real.log y / (100 * theta ^ 2) :=
        div_lt_div_of_pos_right hlogGrowth hdenom
      _ = Real.log y * delta := by
        dsimp [delta]
        ring
  have heightLtExp : (8 : ℝ) < Real.exp 8 := by
    have hexp := Real.add_one_lt_exp (by norm_num : (8 : ℝ) ≠ 0)
    nlinarith
  have heightLePower : (8 : ℝ) ≤ y ^ delta := by
    have hexpLt : Real.exp 8 < Real.exp (Real.log y * delta) :=
      Real.exp_lt_exp.mpr hdeltaLog
    have hrpow : y ^ delta = Real.exp (Real.log y * delta) :=
      Real.rpow_def_of_pos hyPos delta
    rw [hrpow]
    exact (heightLtExp.trans hexpLt).le
  have hexponent : delta + (a + delta) = 1 := by
    dsimp [delta, a, main3BalancedMExponent]
    field_simp [hthetaSqPos.ne']
    ring
  have hpowBudget : 8 * (y ^ a * y ^ delta) ≤ y := by
    calc
      8 * (y ^ a * y ^ delta) = 8 * y ^ (a + delta) := by
        rw [Real.rpow_add hyPos]
      _ ≤ y ^ delta * y ^ (a + delta) :=
        mul_le_mul_of_nonneg_right heightLePower (Real.rpow_nonneg hyPos.le _)
      _ = y ^ (delta + (a + delta)) :=
        (Real.rpow_add hyPos delta (a + delta)).symm
      _ = y := by rw [hexponent]; simp
  have hmeshTimesPower : (M : ℝ) * y ^ delta < P := by
    have hupper : (M : ℝ) * y ^ delta ≤
        (2 * y ^ a) * y ^ delta :=
      mul_le_mul_of_nonneg_right hMupper (Real.rpow_nonneg hyPos.le _)
    have htwo : (2 * y ^ a) * y ^ delta < P := by
      nlinarith
    exact hupper.trans_lt htwo
  have hquotient : y ^ delta ≤ P / (M : ℝ) := by
    exact ((lt_div_iff₀ hMrealPos).2 (by
      simpa only [mul_comm] using hmeshTimesPower)).le
  have hquarter := Real.rpow_le_rpow
    (Real.rpow_nonneg hyPos.le delta) hquotient
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    (Y : ℝ) ^ (1 / (400 * theta ^ 2)) =
        (y ^ delta) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_mul hyPos.le]
      dsimp [y, delta]
      congr 1
      ring
    _ ≤ (P / (M : ℝ)) ^ ((1 : ℝ) / 4) := hquarter
    _ = dyadicBalancedSquareSieveRealScale i
        (main3BalancedM theta Y) := by
      rfl

end

end PellPaper
