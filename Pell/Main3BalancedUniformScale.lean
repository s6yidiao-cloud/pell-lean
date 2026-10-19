import Pell.Main3BalancedNaturalScale
import Pell.UniformBalancedScaleAbsorption
import Mathlib.Tactic

/-!
# Uniform main3 balanced square-sieve scale

This module combines the global growing-parameter absorption lemma with the
actual-cell lower bound for the natural balanced square-sieve scale.  For each
fixed tail threshold `N0`, one uniform eventual cutoff in `Y` supplies both
the determinant growth condition and the two scale inequalities consumed by
the final local box theorem.

This is project-specific parameter bookkeeping.  No analytic estimate is
introduced here.
-/

namespace PellPaper

open Filter

noncomputable section

/-- In the admissible growing-`theta` range, every nonempty actual factor cell
eventually has enough natural square-sieve scale both for the explicit prime
threshold and for an arbitrary fixed tail threshold. -/
theorem eventually_main3Balanced_uniform_scale_package
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 400) :
    ∀ N0 : ℕ,
      ∀ᶠ Y : ℕ in atTop,
        ∀ (theta cellTheta : ℝ) (i : ℕ × ℕ × ℕ × ℕ),
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (dyadicFactorBoxCell cellTheta Y i).Nonempty →
          2 ≤ Y ∧
            Real.exp (800 * theta ^ 2) < (Y : ℝ) ∧
            1280000 * theta ^ 7 *
                (1 + Real.log (2 * (Y : ℝ))) ≤
              dyadicBalancedSquareSieveRealScale i
                (main3BalancedM theta Y) ∧
            N0 ≤ dyadicBalancedSquareSieveScale i
              (main3BalancedM theta Y) := by
  intro N0
  let K : ℝ := max 1280000 (N0 : ℝ)
  have hKpos : 0 < K := by
    exact (by norm_num : (0 : ℝ) < 1280000).trans_le
      (le_max_left 1280000 (N0 : ℝ))
  have hdetSmall : 1600 * c ^ 2 ≤ (1 : ℝ) := by
    nlinarith
  have hAbsReal :=
    eventually_uniform_theta_seventh_log_le_balanced_rpow
      c ((1 : ℝ) / 400) K hc (by norm_num) hKpos hsmall
  have hDetReal :=
    eventually_uniform_exp_eightHundred_theta_sq_lt c hc hdetSmall
  have hAbsNat := tendsto_natCast_atTop_atTop.eventually hAbsReal
  have hDetNat := tendsto_natCast_atTop_atTop.eventually hDetReal
  filter_upwards [hAbsNat, hDetNat, eventually_ge_atTop 2] with
      Y hAbs hDet hY
  intro theta cellTheta i htheta hadmissible hcell
  have hdet := hDet theta htheta hadmissible
  have hscale :=
    nonempty_dyadicFactorBoxCell_main3Balanced_rpow_le_squareSieveRealScale
      theta cellTheta Y i htheta hY hdet hcell
  have habsorbed := hAbs theta htheta hadmissible
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  have htwoYone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Real.log_nonneg htwoYone)
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have hthetaPow : (1 : ℝ) ≤ theta ^ 7 := one_le_pow₀ hthetaOne
  have hfactorOne : (1 : ℝ) ≤ theta ^ 7 * A := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ theta ^ 7 * A :=
        mul_le_mul hthetaPow hAone (by norm_num) (by positivity)
  have hK128 : (1280000 : ℝ) ≤ K := le_max_left _ _
  have hKN0 : (N0 : ℝ) ≤ K := le_max_right _ _
  have hfactor0 : 0 ≤ theta ^ 7 * A := zero_le_one.trans hfactorOne
  have hprime :
      1280000 * theta ^ 7 * A ≤
        dyadicBalancedSquareSieveRealScale i
          (main3BalancedM theta Y) := by
    calc
      1280000 * theta ^ 7 * A =
          (1280000 : ℝ) * (theta ^ 7 * A) := by ring
      _ ≤ K * (theta ^ 7 * A) :=
        mul_le_mul_of_nonneg_right hK128 hfactor0
      _ = K * theta ^ 7 *
          (1 + Real.log (2 * (Y : ℝ))) := by simp only [A, mul_assoc]
      _ ≤ (Y : ℝ) ^ ((1 / 400 : ℝ) / theta ^ 2) := habsorbed
      _ ≤ dyadicBalancedSquareSieveRealScale i
          (main3BalancedM theta Y) := by
        simpa only [div_div] using hscale
  have hN0real :
      (N0 : ℝ) ≤
        (dyadicBalancedSquareSieveScale i
          (main3BalancedM theta Y) : ℝ) := by
    calc
      (N0 : ℝ) ≤ K := hKN0
      _ = K * 1 := by ring
      _ ≤ K * (theta ^ 7 * A) :=
        mul_le_mul_of_nonneg_left hfactorOne hKpos.le
      _ = K * theta ^ 7 *
          (1 + Real.log (2 * (Y : ℝ))) := by simp only [A, mul_assoc]
      _ ≤ (Y : ℝ) ^ ((1 / 400 : ℝ) / theta ^ 2) := habsorbed
      _ ≤ dyadicBalancedSquareSieveRealScale i
          (main3BalancedM theta Y) := by
        simpa only [div_div] using hscale
      _ ≤ (dyadicBalancedSquareSieveScale i
          (main3BalancedM theta Y) : ℝ) :=
        dyadicBalancedSquareSieveRealScale_le_natScale _ _
  refine ⟨hY, hdet, ?_, ?_⟩
  · simpa only [A] using hprime
  · exact_mod_cast hN0real

end

end PellPaper
