import Pell.BinaryLinearSubstitutionNatHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Ceiling parameters for the main3 balanced range

This module records the literal choices

`B = ceil(theta^2)` and `M = ceil(Y^(1 - 1/(50 theta^2)))`

from the balanced part of the manuscript.  It proves the near-square degree
window and the complete elementary localization-exponent package.  No Pell
geometry, determinant estimate, or square-sieve estimate occurs here.
-/

namespace PellPaper

noncomputable section

/-- The exponent in `M_b = ceil(Y^(1-2*kappa/theta^2))` for
`kappa = 1/100`. -/
def main3BalancedMExponent (theta : ℝ) : ℝ :=
  1 - 1 / (50 * theta ^ 2)

/-- The main3 balanced localization mesh. -/
def main3BalancedM (theta : ℝ) (Y : ℕ) : ℕ :=
  ⌈((Y : ℝ) ^ main3BalancedMExponent theta)⌉₊

/-- The exact logarithmic exponent of the integer ceiling mesh. -/
def main3BalancedMLogExponent (theta : ℝ) (Y : ℕ) : ℝ :=
  Real.log (main3BalancedM theta Y : ℝ) / Real.log (Y : ℝ)

/-- The common near-square auxiliary degree in main3. -/
def main3BalancedDegree (theta : ℝ) : ℕ :=
  ⌈theta ^ 2⌉₊

/-- The ceiling degree lies in the exact near-square window used by the fan
numerics. -/
theorem main3BalancedDegree_nearSquare
    (theta : ℝ) :
    theta ^ 2 ≤ (main3BalancedDegree theta : ℝ) ∧
      (main3BalancedDegree theta : ℝ) < theta ^ 2 + 1 := by
  constructor
  · exact Nat.le_ceil (theta ^ 2)
  · exact Nat.ceil_lt_add_one (sq_nonneg theta)

/-- The real exponent defining the localization mesh lies between `9/10`
and one throughout the numerical range `theta >= 3`. -/
theorem main3BalancedMExponent_mem
    {theta : ℝ} (htheta : 3 ≤ theta) :
    9 / 10 ≤ main3BalancedMExponent theta ∧
      main3BalancedMExponent theta ≤ 1 := by
  have hthetaSq : 9 ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hdenom : 0 < 50 * theta ^ 2 := by positivity
  unfold main3BalancedMExponent
  constructor
  · have hfrac : (1 : ℝ) / (50 * theta ^ 2) ≤ 1 / 10 := by
      apply (div_le_iff₀ hdenom).2
      nlinarith
    linarith
  · have : 0 ≤ (1 : ℝ) / (50 * theta ^ 2) := by positivity
    linarith

/-- Complete elementary package for the integer mesh and its exact
logarithmic exponent. -/
theorem main3BalancedM_parameter_package
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    let M := main3BalancedM theta Y
    let m := main3BalancedMLogExponent theta Y
    0 < M ∧ M ≤ Y ∧
      9 / 10 ≤ m ∧ m ≤ 1 ∧
      (1 - m) * theta ^ 2 ≤ 1 / 50 ∧
      m * Real.log (Y : ℝ) = Real.log (M : ℝ) := by
  let a : ℝ := main3BalancedMExponent theta
  let M : ℕ := main3BalancedM theta Y
  let m : ℝ := main3BalancedMLogExponent theta Y
  have ha := main3BalancedMExponent_mem htheta
  have haLower : (9 / 10 : ℝ) ≤ a := by simpa only [a] using ha.1
  have haUpper : a ≤ 1 := by simpa only [a] using ha.2
  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 9 / 10).trans haLower
  have hYoneNat : 1 ≤ Y := by omega
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hYoneNat
  have hYpos : (0 : ℝ) < (Y : ℝ) := zero_lt_one.trans_le hYone
  have hlogYpos : 0 < Real.log (Y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Y by omega)
  have hrpowPos : 0 < (Y : ℝ) ^ a :=
    Real.rpow_pos_of_pos hYpos a
  have hMpos : 0 < M := by
    dsimp [M, main3BalancedM]
    exact Nat.ceil_pos.mpr (by simpa only [a] using hrpowPos)
  have hrpowUpper : (Y : ℝ) ^ a ≤ (Y : ℝ) := by
    calc
      (Y : ℝ) ^ a ≤ (Y : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYone haUpper
      _ = (Y : ℝ) := by simp
  have hMle : M ≤ Y := by
    dsimp [M, main3BalancedM]
    exact Nat.ceil_le.mpr (by simpa only [a] using hrpowUpper)
  have hrpowM : (Y : ℝ) ^ a ≤ (M : ℝ) := by
    dsimp [M, main3BalancedM]
    simpa only [a] using Nat.le_ceil ((Y : ℝ) ^ main3BalancedMExponent theta)
  have hMrealPos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hlogLower : a * Real.log (Y : ℝ) ≤ Real.log (M : ℝ) := by
    have hlog := Real.log_le_log hrpowPos hrpowM
    rw [Real.log_rpow hYpos] at hlog
    exact hlog
  have hmLowerA : a ≤ m := by
    dsimp [m, main3BalancedMLogExponent]
    exact (le_div_iff₀ hlogYpos).2 hlogLower
  have hmLower : (9 / 10 : ℝ) ≤ m := haLower.trans hmLowerA
  have hMcastLe : (M : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hMle
  have hlogUpper : Real.log (M : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hMrealPos hMcastLe
  have hmUpper : m ≤ 1 := by
    dsimp [m, main3BalancedMLogExponent]
    apply (div_le_iff₀ hlogYpos).2
    simpa using hlogUpper
  have hthetaSqPos : 0 < theta ^ 2 := by positivity
  have hdefectA : (1 - a) * theta ^ 2 = (1 : ℝ) / 50 := by
    dsimp [a, main3BalancedMExponent]
    field_simp
    ring
  have hdefect : (1 - m) * theta ^ 2 ≤ (1 : ℝ) / 50 := by
    calc
      (1 - m) * theta ^ 2 ≤ (1 - a) * theta ^ 2 := by
        exact mul_le_mul_of_nonneg_right (sub_le_sub_left hmLowerA 1)
          hthetaSqPos.le
      _ = (1 : ℝ) / 50 := hdefectA
  have hmLog : m * Real.log (Y : ℝ) = Real.log (M : ℝ) := by
    change (Real.log (M : ℝ) / Real.log (Y : ℝ)) *
      Real.log (Y : ℝ) = Real.log (M : ℝ)
    field_simp [hlogYpos.ne']
  dsimp only
  exact ⟨hMpos, hMle, hmLower, hmUpper, hdefect,
    by simpa only [M] using hmLog⟩

end

end PellPaper
