import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Uniform absorption at the balanced Pell scale

The balanced range has
`theta ≤ c * sqrt (log Z / log (log Z))`.  This module records the
elementary uniform consequences needed by the global argument.  In
particular, when `10 * c^2 ≤ kappa`, the moving power
`Z^(kappa / theta^2)` absorbs `K * theta^7 * (1 + log (2Z))` uniformly in
every admissible `theta`.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Squaring the balanced admissibility condition and clearing the positive
`log (log Z)` denominator.  This is the algebraic core shared by both
uniform absorption statements below. -/
theorem theta_sq_mul_log_log_le_of_balanced_admissible
    (c theta Z : ℝ)
    (hc : 0 ≤ c) (htheta : 0 ≤ theta)
    (hlog : 0 ≤ Real.log Z)
    (hloglog : 0 < Real.log (Real.log Z))
    (hadmissible :
      theta ≤ c * Real.sqrt
        (Real.log Z / Real.log (Real.log Z))) :
    theta ^ 2 * Real.log (Real.log Z) ≤
      c ^ 2 * Real.log Z := by
  have hratio : 0 ≤ Real.log Z / Real.log (Real.log Z) :=
    div_nonneg hlog hloglog.le
  have hsqrt :
      (Real.sqrt (Real.log Z / Real.log (Real.log Z))) ^ 2 =
        Real.log Z / Real.log (Real.log Z) :=
    Real.sq_sqrt hratio
  have hright :
      0 ≤ c * Real.sqrt (Real.log Z / Real.log (Real.log Z)) :=
    mul_nonneg hc (Real.sqrt_nonneg _)
  have hsquare :
      theta ^ 2 ≤
        (c * Real.sqrt
          (Real.log Z / Real.log (Real.log Z))) ^ 2 :=
    pow_le_pow_left₀ htheta hadmissible 2
  rw [mul_pow, hsqrt] at hsquare
  have hcleared :
      theta ^ 2 ≤
        (c ^ 2 * Real.log Z) / Real.log (Real.log Z) := by
    calc
      theta ^ 2 ≤ c ^ 2 *
          (Real.log Z / Real.log (Real.log Z)) := hsquare
      _ = (c ^ 2 * Real.log Z) / Real.log (Real.log Z) := by ring
  exact (le_div_iff₀ hloglog).1 hcleared

/-- Uniform manuscript absorption.  The outer threshold in `Z` depends only
on the fixed constants `c`, `kappa`, and `K`; all admissible `theta` are
quantified afterwards.  The safe relation `10*c^2 ≤ kappa` leaves two
powers of `log Z` to absorb the fixed coefficient. -/
theorem eventually_uniform_theta_seventh_log_le_balanced_rpow
    (c kappa K : ℝ)
    (hc : 0 < c) (hkappa : 0 < kappa) (hK : 0 < K)
    (hsmall : 10 * c ^ 2 ≤ kappa) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log Z / Real.log (Real.log Z)) →
        K * theta ^ 7 * (1 + Real.log (2 * Z)) ≤
          Z ^ (kappa / theta ^ 2) := by
  let A : ℝ := 3 * K * c ^ 7
  let Z0 : ℝ :=
    max (Real.exp (Real.exp 1)) (Real.exp (max 1 A))
  filter_upwards [eventually_ge_atTop Z0] with Z hZ
  intro theta htheta hadmissible
  have hZbase : Real.exp (Real.exp 1) ≤ Z :=
    (le_max_left _ _).trans hZ
  have hZconstant : Real.exp (max 1 A) ≤ Z :=
    (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := (Real.exp_pos _).trans_le hZbase
  have hlogExp : Real.exp 1 ≤ Real.log Z := by
    exact (Real.le_log_iff_exp_le hZpos).2 hZbase
  have hlogpos : 0 < Real.log Z := (Real.exp_pos _).trans_le hlogExp
  have hlogone : 1 ≤ Real.log Z := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hlogExp
  have hloglogone : 1 ≤ Real.log (Real.log Z) := by
    exact (Real.le_log_iff_exp_le hlogpos).2 hlogExp
  have hloglogpos : 0 < Real.log (Real.log Z) :=
    zero_lt_one.trans_le hloglogone
  have htheta0 : 0 ≤ theta := by linarith
  have hthetaSqLog :=
    theta_sq_mul_log_log_le_of_balanced_admissible
      c theta Z hc.le htheta0 hlogpos.le hloglogpos hadmissible
  have hten :
      10 * theta ^ 2 * Real.log (Real.log Z) ≤
        kappa * Real.log Z := by
    calc
      10 * theta ^ 2 * Real.log (Real.log Z) ≤
          10 * (c ^ 2 * Real.log Z) := by nlinarith
      _ = (10 * c ^ 2) * Real.log Z := by ring
      _ ≤ kappa * Real.log Z :=
        mul_le_mul hsmall (le_refl _) hlogpos.le hkappa.le
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos (by linarith)
  have hexponent :
      10 * Real.log (Real.log Z) ≤
        Real.log Z * (kappa / theta ^ 2) := by
    rw [show Real.log Z * (kappa / theta ^ 2) =
      (kappa * Real.log Z) / theta ^ 2 by ring]
    apply (le_div_iff₀ hthetaSqPos).2
    nlinarith
  have hrpowLower :
      (Real.log Z) ^ 10 ≤ Z ^ (kappa / theta ^ 2) := by
    calc
      (Real.log Z) ^ 10 =
          Real.exp (10 * Real.log (Real.log Z)) := by
        rw [show 10 * Real.log (Real.log Z) =
          Real.log (Real.log Z) * (10 : ℝ) by ring]
        rw [← Real.rpow_def_of_pos hlogpos]
        norm_num [Real.rpow_natCast]
      _ ≤ Real.exp (Real.log Z * (kappa / theta ^ 2)) :=
        Real.exp_le_exp.mpr hexponent
      _ = Z ^ (kappa / theta ^ 2) :=
        (Real.rpow_def_of_pos hZpos _).symm
  have hlogconstant : max 1 A ≤ Real.log Z := by
    exact (Real.le_log_iff_exp_le hZpos).2 hZconstant
  have hAleLog : A ≤ Real.log Z :=
    (le_max_right (1 : ℝ) A).trans hlogconstant
  have hratioLe :
      Real.log Z / Real.log (Real.log Z) ≤ Real.log Z := by
    apply (div_le_iff₀ hloglogpos).2
    have hproduct :
        0 ≤ Real.log Z * (Real.log (Real.log Z) - 1) :=
      mul_nonneg hlogpos.le (sub_nonneg.mpr hloglogone)
    nlinarith
  have hsqrtLeLog :
      Real.sqrt (Real.log Z / Real.log (Real.log Z)) ≤ Real.log Z := by
    have hratio0 :
        0 ≤ Real.log Z / Real.log (Real.log Z) :=
      div_nonneg hlogpos.le hloglogpos.le
    have hsqrtLeSqrt :
        Real.sqrt (Real.log Z / Real.log (Real.log Z)) ≤
          Real.sqrt (Real.log Z) := Real.sqrt_le_sqrt hratioLe
    have hsqrtLogLe : Real.sqrt (Real.log Z) ≤ Real.log Z := by
      rw [Real.sqrt_le_iff]
      exact ⟨hlogpos.le, by nlinarith [hlogone]⟩
    exact hsqrtLeSqrt.trans hsqrtLogLe
  have hthetaLe : theta ≤ c * Real.log Z :=
    hadmissible.trans
      (mul_le_mul_of_nonneg_left hsqrtLeLog hc.le)
  have hthetaPow : theta ^ 7 ≤ (c * Real.log Z) ^ 7 :=
    pow_le_pow_left₀ htheta0 hthetaLe 7
  have hlogProduct :
      1 + Real.log (2 * Z) ≤ 3 * Real.log Z := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
    nlinarith [Real.log_two_lt_d9.le]
  have hlogProduct0 : 0 ≤ 1 + Real.log (2 * Z) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
    have hlogtwo0 : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    linarith
  have hleft :
      K * theta ^ 7 * (1 + Real.log (2 * Z)) ≤
        A * (Real.log Z) ^ 8 := by
    calc
      K * theta ^ 7 * (1 + Real.log (2 * Z)) ≤
          K * (c * Real.log Z) ^ 7 * (3 * Real.log Z) := by
        gcongr
      _ = A * (Real.log Z) ^ 8 := by
        dsimp [A]
        ring
  calc
    K * theta ^ 7 * (1 + Real.log (2 * Z)) ≤
        A * (Real.log Z) ^ 8 := hleft
    _ ≤ (Real.log Z) ^ 2 * (Real.log Z) ^ 8 := by
      gcongr
      nlinarith [mul_nonneg hlogpos.le (sub_nonneg.mpr hlogone)]
    _ = (Real.log Z) ^ 10 := by ring
    _ ≤ Z ^ (kappa / theta ^ 2) := hrpowLower

/-- The same admissible range forces the fixed determinant-cost threshold
`exp (800*theta^2) < Z` uniformly.  The explicit condition
`1600*c^2 ≤ 1` reserves a factor `1/2` in the logarithmic exponent. -/
theorem eventually_uniform_exp_eightHundred_theta_sq_lt
    (c : ℝ) (hc : 0 < c) (hsmall : 1600 * c ^ 2 ≤ 1) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log Z / Real.log (Real.log Z)) →
        Real.exp (800 * theta ^ 2) < Z := by
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with Z hZ
  intro theta htheta hadmissible
  have hZpos : 0 < Z := (Real.exp_pos _).trans_le hZ
  have hlogExp : Real.exp 1 ≤ Real.log Z := by
    exact (Real.le_log_iff_exp_le hZpos).2 hZ
  have hlogpos : 0 < Real.log Z := (Real.exp_pos _).trans_le hlogExp
  have hloglogone : 1 ≤ Real.log (Real.log Z) := by
    exact (Real.le_log_iff_exp_le hlogpos).2 hlogExp
  have hloglogpos : 0 < Real.log (Real.log Z) :=
    zero_lt_one.trans_le hloglogone
  have htheta0 : 0 ≤ theta := by linarith
  have hthetaSqLog :=
    theta_sq_mul_log_log_le_of_balanced_admissible
      c theta Z hc.le htheta0 hlogpos.le hloglogpos hadmissible
  have hthetaSq : theta ^ 2 ≤ c ^ 2 * Real.log Z := by
    nlinarith [mul_nonneg (sq_nonneg theta)
      (sub_nonneg.mpr hloglogone)]
  have hexponent : 800 * theta ^ 2 < Real.log Z := by
    have hc800 : 800 * c ^ 2 ≤ 1 / 2 := by nlinarith
    have : 800 * theta ^ 2 ≤ (1 / 2 : ℝ) * Real.log Z := by
      calc
        800 * theta ^ 2 ≤ 800 * (c ^ 2 * Real.log Z) := by nlinarith
        _ = (800 * c ^ 2) * Real.log Z := by ring
        _ ≤ (1 / 2 : ℝ) * Real.log Z :=
          mul_le_mul_of_nonneg_right hc800 hlogpos.le
    linarith
  calc
    Real.exp (800 * theta ^ 2) < Real.exp (Real.log Z) :=
      Real.exp_lt_exp.mpr hexponent
    _ = Z := Real.exp_log hZpos

end

end PellPaper
