import Pell.Main3BalancedCeilingParameters
import Pell.PowerRootBandEndpoints
import Mathlib.Tactic

/-!
# The natural main3 balanced-range threshold

The balanced/unbalanced split in the manuscript uses

`R = ceil (Y^(1/(100*theta^2)))`.

This module records the literal natural threshold, its rounding bounds, and
its exact comparison with the canonical localization mesh
`M = ceil (Y^(1-1/(50*theta^2)))`.  The product `R^2 M` is trapped between
`Y` and `8Y`; the factor eight is solely the three ceiling losses.
-/

namespace PellPaper

noncomputable section

/-- The exponent `kappa/theta^2` for the main3 choice `kappa=1/100`. -/
def main3BalancedRExponent (theta : ℝ) : ℝ :=
  1 / (100 * theta ^ 2)

/-- The upward-rounded natural balanced-range threshold. -/
def main3BalancedR (theta : ℝ) (Y : ℕ) : ℕ :=
  powerRootCeilEndpoint Y (main3BalancedRExponent theta)

theorem main3BalancedRExponent_pos {theta : ℝ} (htheta : 3 ≤ theta) :
    0 < main3BalancedRExponent theta := by
  unfold main3BalancedRExponent
  positivity

/-- The two threshold exponents and the mesh exponent add to one exactly. -/
theorem two_mul_main3BalancedRExponent_add_MExponent (theta : ℝ)
    (htheta : 3 ≤ theta) :
    2 * main3BalancedRExponent theta + main3BalancedMExponent theta = 1 := by
  have hthetaSq : 0 < theta ^ 2 := by positivity
  unfold main3BalancedRExponent main3BalancedMExponent
  field_simp [hthetaSq.ne']
  ring

/-- Complete rounding package for the natural balanced threshold. -/
theorem main3BalancedR_parameter_package
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    let r := (Y : ℝ) ^ main3BalancedRExponent theta
    let R := main3BalancedR theta Y
    1 ≤ R ∧ r ≤ (R : ℝ) ∧ (R : ℝ) ≤ 2 * r ∧ R ≤ Y := by
  let delta : ℝ := main3BalancedRExponent theta
  let r : ℝ := (Y : ℝ) ^ delta
  let R : ℕ := main3BalancedR theta Y
  have hYoneNat : 1 ≤ Y := by omega
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hYoneNat
  have hdeltaPos : 0 < delta := by
    simpa only [delta] using main3BalancedRExponent_pos htheta
  have hrOne : 1 ≤ r := by
    dsimp [r]
    exact Real.one_le_rpow hYone hdeltaPos.le
  have hRone : 1 ≤ R := by
    dsimp [R, main3BalancedR]
    exact one_le_powerRootCeilEndpoint hYoneNat delta
  have hrR : r ≤ (R : ℝ) := by
    dsimp [r, R, main3BalancedR]
    exact rpow_le_powerRootCeilEndpoint Y delta
  have hRtwo : (R : ℝ) ≤ 2 * r := by
    dsimp [R, main3BalancedR]
    simpa only [r] using
      powerRootCeilEndpoint_le_two_rpow hYoneNat hdeltaPos.le
  have hthetaSq : 9 ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hdenom : 0 < 100 * theta ^ 2 := by positivity
  have hdeltaOne : delta ≤ 1 := by
    dsimp [delta, main3BalancedRExponent]
    apply (div_le_iff₀ hdenom).2
    nlinarith
  have hrY : r ≤ (Y : ℝ) := by
    dsimp [r]
    calc
      (Y : ℝ) ^ delta ≤ (Y : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYone hdeltaOne
      _ = (Y : ℝ) := by simp
  have hRY : R ≤ Y := by
    dsimp [R, main3BalancedR, powerRootCeilEndpoint]
    exact Nat.ceil_le.mpr (by simpa only [r] using hrY)
  dsimp only
  exact ⟨hRone, hrR, hRtwo, hRY⟩

/-- The canonical ceiling mesh is within a factor two of its defining real
power, a sharpening of the coarser `M ≤ Y` package. -/
theorem main3BalancedM_sharp_bounds
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    let m0 := (Y : ℝ) ^ main3BalancedMExponent theta
    let M := main3BalancedM theta Y
    0 < M ∧ m0 ≤ (M : ℝ) ∧ (M : ℝ) ≤ 2 * m0 := by
  let a : ℝ := main3BalancedMExponent theta
  let m0 : ℝ := (Y : ℝ) ^ a
  let M : ℕ := main3BalancedM theta Y
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ Y by omega)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact (by norm_num : (0 : ℝ) ≤ 9 / 10).trans
      (main3BalancedMExponent_mem htheta).1
  have hm0One : 1 ≤ m0 := by
    dsimp [m0]
    exact Real.one_le_rpow hYone ha0
  have hMpos : 0 < M := by
    simpa only [M] using
      (main3BalancedM_parameter_package theta Y htheta hY).1
  have hm0M : m0 ≤ (M : ℝ) := by
    dsimp [m0, M, main3BalancedM]
    exact Nat.le_ceil ((Y : ℝ) ^ a)
  have hMlt : (M : ℝ) < m0 + 1 := by
    dsimp [m0, M, main3BalancedM]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg Y) a)
  have hMtwo : (M : ℝ) ≤ 2 * m0 := hMlt.le.trans (by linarith)
  dsimp only
  exact ⟨hMpos, hm0M, hMtwo⟩

/-- The rounded threshold and rounded mesh retain the exact scale relation,
with at most a factor eight from two copies of `R` and one copy of `M`. -/
theorem main3BalancedR_sq_mul_M_comparable
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (Y : ℝ) ≤ (main3BalancedR theta Y : ℝ) ^ 2 *
        (main3BalancedM theta Y : ℝ) ∧
      (main3BalancedR theta Y : ℝ) ^ 2 *
        (main3BalancedM theta Y : ℝ) ≤ 8 * (Y : ℝ) := by
  let y : ℝ := Y
  let delta : ℝ := main3BalancedRExponent theta
  let a : ℝ := main3BalancedMExponent theta
  let r : ℝ := y ^ delta
  let m0 : ℝ := y ^ a
  let R : ℕ := main3BalancedR theta Y
  let M : ℕ := main3BalancedM theta Y
  have hyPos : 0 < y := by dsimp [y]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hm00 : 0 ≤ m0 := by dsimp [m0]; positivity
  have hR := main3BalancedR_parameter_package theta Y htheta hY
  have hM := main3BalancedM_sharp_bounds theta Y htheta hY
  have hrR : r ≤ (R : ℝ) := by simpa only [r, R] using hR.2.1
  have hRtwo : (R : ℝ) ≤ 2 * r := by simpa only [r, R] using hR.2.2.1
  have hm0M : m0 ≤ (M : ℝ) := by simpa only [m0, M] using hM.2.1
  have hMtwo : (M : ℝ) ≤ 2 * m0 := by simpa only [m0, M] using hM.2.2
  have hexponent : delta + delta + a = 1 := by
    have h := two_mul_main3BalancedRExponent_add_MExponent theta htheta
    dsimp [delta, a] at h ⊢
    linarith
  have hscale : r ^ 2 * m0 = y := by
    dsimp [r, m0]
    rw [pow_two, ← Real.rpow_add hyPos, ← Real.rpow_add hyPos]
    rw [hexponent]
    simp
  constructor
  · calc
      y = r ^ 2 * m0 := hscale.symm
      _ ≤ (R : ℝ) ^ 2 * (M : ℝ) := by
        gcongr
  · calc
      (R : ℝ) ^ 2 * (M : ℝ) ≤ (2 * r) ^ 2 * (2 * m0) := by
        gcongr
      _ = 8 * y := by rw [← hscale]; ring

end

end PellPaper
