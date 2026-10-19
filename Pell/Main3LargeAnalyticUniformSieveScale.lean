import Pell.UniformBalancedScaleAbsorption
import Pell.PowerRootBandEndpoints
import Mathlib.Tactic

/-!
# Uniform sieve scale for the Main3 large-analytic range

We use the deliberately simple scale
`ceil(Y^(1/(32 theta^2)))`.  It is independent of blocks, keys, cells, and
selected covers, while eventually absorbing both any fixed global sieve
cutoff and the explicit Main3 logarithmic threshold.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The common large-analytic square-sieve parameter. -/
noncomputable def main3LargeAnalyticSieveN (theta : ℝ) (Y : ℕ) : ℕ :=
  powerRootCeilEndpoint Y (1 / (32 * theta ^ 2))

/-- The defining real scale lies below its rounded natural parameter. -/
theorem main3LargeAnalyticSieveRealScale_le
    (theta : ℝ) (Y : ℕ) :
    (Y : ℝ) ^ (1 / (32 * theta ^ 2)) ≤
      (main3LargeAnalyticSieveN theta Y : ℝ) := by
  exact rpow_le_powerRootCeilEndpoint Y (1 / (32 * theta ^ 2))

/-- In the final admissible growing-parameter range, one scale works
uniformly after every fixed cutoff `N₀`. -/
theorem eventually_main3LargeAnalytic_uniformSieveScale_package
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) (N₀ : ℕ) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      3 ≤ theta →
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      Real.exp (800 * theta ^ 2) < (Y : ℝ) ∧
        4 ≤ main3LargeAnalyticSieveN theta Y ∧
        N₀ ≤ main3LargeAnalyticSieveN theta Y ∧
        128000 * theta ^ 7 * Real.log (Y : ℝ) ≤
          (main3LargeAnalyticSieveN theta Y : ℝ) ∧
        (main3LargeAnalyticSieveN theta Y : ℝ) ≤
          2 * (Y : ℝ) ^ (1 / (32 * theta ^ 2)) := by
  let K : ℝ := max 128000 (N₀ : ℝ)
  have hKpos : 0 < K :=
    (by norm_num : (0 : ℝ) < 128000).trans_le (le_max_left _ _)
  have habsSmall : 10 * c ^ 2 ≤ (1 : ℝ) / 32 := by
    exact hsmall.trans (by norm_num)
  have hdetSmall : 1600 * c ^ 2 ≤ (1 : ℝ) := by
    nlinarith
  have hAbsReal :=
    eventually_uniform_theta_seventh_log_le_balanced_rpow
      c ((1 : ℝ) / 32) K hc (by norm_num) hKpos habsSmall
  have hDetReal :=
    eventually_uniform_exp_eightHundred_theta_sq_lt c hc hdetSmall
  have hAbsNat := tendsto_natCast_atTop_atTop.eventually hAbsReal
  have hDetNat := tendsto_natCast_atTop_atTop.eventually hDetReal
  filter_upwards [hAbsNat, hDetNat, eventually_ge_atTop 2] with
      Y hAbs hDet hY
  intro theta htheta hadmissible
  have hdet := hDet theta htheta hadmissible
  have habs := hAbs theta htheta hadmissible
  let a : ℝ := 1 / (32 * theta ^ 2)
  let P : ℕ := main3LargeAnalyticSieveN theta Y
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  have htheta0 : 0 ≤ theta := by linarith
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have hthetaPow : (1 : ℝ) ≤ theta ^ 7 := one_le_pow₀ hthetaOne
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hYone : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  have htwoYone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hAone : 1 ≤ A := by
    dsimp only [A]
    exact le_add_of_nonneg_right (Real.log_nonneg htwoYone)
  have hA0 : 0 ≤ A := zero_le_one.trans hAone
  have hfactorOne : (1 : ℝ) ≤ theta ^ 7 * A := by
    nlinarith [mul_le_mul hthetaPow hAone (by norm_num) (by positivity)]
  have hK128 : (128000 : ℝ) ≤ K := le_max_left _ _
  have hKN₀ : (N₀ : ℝ) ≤ K := le_max_right _ _
  have hscale : K * theta ^ 7 * A ≤ (Y : ℝ) ^ a := by
    simpa only [a, A, div_div] using habs
  have hrpowP : (Y : ℝ) ^ a ≤ (P : ℝ) := by
    simpa only [P, a] using main3LargeAnalyticSieveRealScale_le theta Y
  have hN₀real : (N₀ : ℝ) ≤ (P : ℝ) := by
    calc
      (N₀ : ℝ) ≤ K := hKN₀
      _ = K * 1 := by ring
      _ ≤ K * (theta ^ 7 * A) :=
        mul_le_mul_of_nonneg_left hfactorOne hKpos.le
      _ = K * theta ^ 7 * A := by ring
      _ ≤ (Y : ℝ) ^ a := hscale
      _ ≤ (P : ℝ) := hrpowP
  have hfourReal : (4 : ℝ) ≤ (P : ℝ) := by
    calc
      (4 : ℝ) ≤ 128000 := by norm_num
      _ ≤ K := hK128
      _ = K * 1 := by ring
      _ ≤ K * (theta ^ 7 * A) :=
        mul_le_mul_of_nonneg_left hfactorOne hKpos.le
      _ = K * theta ^ 7 * A := by ring
      _ ≤ (Y : ℝ) ^ a := hscale
      _ ≤ (P : ℝ) := hrpowP
  have hlogY : Real.log (Y : ℝ) ≤ A := by
    have hlogMono : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
      Real.log_le_log hYpos (by nlinarith)
    dsimp only [A]
    linarith
  have hprime : 128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (P : ℝ) := by
    calc
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤
          128000 * theta ^ 7 * A := by
        gcongr
      _ ≤ K * theta ^ 7 * A := by
        gcongr
      _ ≤ (Y : ℝ) ^ a := hscale
      _ ≤ (P : ℝ) := hrpowP
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hPupper : (P : ℝ) ≤ 2 * (Y : ℝ) ^ a := by
    simpa only [P, a, main3LargeAnalyticSieveN] using
      powerRootCeilEndpoint_le_two_rpow (show 1 ≤ Y by omega) ha0
  exact ⟨hdet, by exact_mod_cast hfourReal, by exact_mod_cast hN₀real,
    by simpa only [P] using hprime, by simpa only [P, a] using hPupper⟩

end

end PellPaper

