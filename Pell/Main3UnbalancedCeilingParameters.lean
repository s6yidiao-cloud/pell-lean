import Pell.Main3BalancedCeilingParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Ceiling parameters for the main3 large-analytic unbalanced range

This module records the manuscript choices

`m_u = 1 - 1 / (8 * theta^2)` and `M_u = ceil(Y^m_u)`

corresponding to `beta_u = 1/8`.  It proves the sharp exponent interval
`71/72 <= m_u <= 1` for `theta >= 3`, together with the complete elementary
package for the integer ceiling and its exact logarithmic exponent.  The
auxiliary degree remains the already defined `ceil(theta^2)`.

No shifted-square estimate, error absorption, cell construction, or
determinant argument occurs here.
-/

namespace PellPaper

noncomputable section

/-- The large-analytic localization exponent for `beta_u = 1/8`. -/
def main3UnbalancedMExponent (theta : ℝ) : ℝ :=
  1 - 1 / (8 * theta ^ 2)

/-- The large-analytic localization mesh. -/
def main3UnbalancedM (theta : ℝ) (Y : ℕ) : ℕ :=
  ⌈((Y : ℝ) ^ main3UnbalancedMExponent theta)⌉₊

/-- The exact logarithmic exponent of the integer ceiling mesh. -/
def main3UnbalancedMLogExponent (theta : ℝ) (Y : ℕ) : ℝ :=
  Real.log (main3UnbalancedM theta Y : ℝ) / Real.log (Y : ℝ)

/-- The defining real exponent lies in the manuscript interval. -/
theorem main3UnbalancedMExponent_mem
    {theta : ℝ} (htheta : 3 ≤ theta) :
    71 / 72 ≤ main3UnbalancedMExponent theta ∧
      main3UnbalancedMExponent theta ≤ 1 := by
  have hthetaSq : 9 ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hdenom : 0 < 8 * theta ^ 2 := by positivity
  unfold main3UnbalancedMExponent
  constructor
  · have hfrac : (1 : ℝ) / (8 * theta ^ 2) ≤ 1 / 72 := by
      apply (div_le_iff₀ hdenom).2
      nlinarith
    linarith
  · have : 0 ≤ (1 : ℝ) / (8 * theta ^ 2) := by positivity
    linarith

/-- Complete elementary package for the unbalanced integer mesh and its exact
logarithmic exponent. -/
theorem main3UnbalancedM_parameter_package
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    let M := main3UnbalancedM theta Y
    let m := main3UnbalancedMLogExponent theta Y
    0 < M ∧ M ≤ Y ∧
      71 / 72 ≤ m ∧ m ≤ 1 ∧
      (1 - m) * theta ^ 2 ≤ 1 / 8 ∧
      m * Real.log (Y : ℝ) = Real.log (M : ℝ) := by
  let a : ℝ := main3UnbalancedMExponent theta
  let M : ℕ := main3UnbalancedM theta Y
  let m : ℝ := main3UnbalancedMLogExponent theta Y
  have ha := main3UnbalancedMExponent_mem htheta
  have haLower : (71 / 72 : ℝ) ≤ a := by simpa only [a] using ha.1
  have haUpper : a ≤ 1 := by simpa only [a] using ha.2
  have ha0 : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 71 / 72).trans haLower
  have hYoneNat : 1 ≤ Y := by omega
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hYoneNat
  have hYpos : (0 : ℝ) < (Y : ℝ) := zero_lt_one.trans_le hYone
  have hlogYpos : 0 < Real.log (Y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Y by omega)
  have hrpowPos : 0 < (Y : ℝ) ^ a :=
    Real.rpow_pos_of_pos hYpos a
  have hMpos : 0 < M := by
    dsimp [M, main3UnbalancedM]
    exact Nat.ceil_pos.mpr (by simpa only [a] using hrpowPos)
  have hrpowUpper : (Y : ℝ) ^ a ≤ (Y : ℝ) := by
    calc
      (Y : ℝ) ^ a ≤ (Y : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYone haUpper
      _ = (Y : ℝ) := by simp
  have hMle : M ≤ Y := by
    dsimp [M, main3UnbalancedM]
    exact Nat.ceil_le.mpr (by simpa only [a] using hrpowUpper)
  have hrpowM : (Y : ℝ) ^ a ≤ (M : ℝ) := by
    dsimp [M, main3UnbalancedM]
    simpa only [a] using Nat.le_ceil ((Y : ℝ) ^ main3UnbalancedMExponent theta)
  have hMrealPos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hlogLower : a * Real.log (Y : ℝ) ≤ Real.log (M : ℝ) := by
    have hlog := Real.log_le_log hrpowPos hrpowM
    rw [Real.log_rpow hYpos] at hlog
    exact hlog
  have hmLowerA : a ≤ m := by
    dsimp [m, main3UnbalancedMLogExponent]
    exact (le_div_iff₀ hlogYpos).2 hlogLower
  have hmLower : (71 / 72 : ℝ) ≤ m := haLower.trans hmLowerA
  have hMcastLe : (M : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hMle
  have hlogUpper : Real.log (M : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hMrealPos hMcastLe
  have hmUpper : m ≤ 1 := by
    dsimp [m, main3UnbalancedMLogExponent]
    apply (div_le_iff₀ hlogYpos).2
    simpa using hlogUpper
  have hthetaSqPos : 0 < theta ^ 2 := by positivity
  have hdefectA : (1 - a) * theta ^ 2 = (1 : ℝ) / 8 := by
    dsimp [a, main3UnbalancedMExponent]
    field_simp
    ring
  have hdefect : (1 - m) * theta ^ 2 ≤ (1 : ℝ) / 8 := by
    calc
      (1 - m) * theta ^ 2 ≤ (1 - a) * theta ^ 2 := by
        exact mul_le_mul_of_nonneg_right (sub_le_sub_left hmLowerA 1)
          hthetaSqPos.le
      _ = (1 : ℝ) / 8 := hdefectA
  have hmLog : m * Real.log (Y : ℝ) = Real.log (M : ℝ) := by
    change (Real.log (M : ℝ) / Real.log (Y : ℝ)) *
      Real.log (Y : ℝ) = Real.log (M : ℝ)
    field_simp [hlogYpos.ne']
  dsimp only
  exact ⟨hMpos, hMle, hmLower, hmUpper, hdefect,
    by simpa only [M] using hmLog⟩

/-- The unbalanced route reuses the common degree `ceil(theta^2)`. -/
theorem main3UnbalancedDegree_nearSquare (theta : ℝ) :
    theta ^ 2 ≤ (main3BalancedDegree theta : ℝ) ∧
      (main3BalancedDegree theta : ℝ) < theta ^ 2 + 1 :=
  main3BalancedDegree_nearSquare theta

end

end PellPaper
