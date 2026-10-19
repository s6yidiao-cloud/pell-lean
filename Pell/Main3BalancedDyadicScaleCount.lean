import Pell.DyadicBoxReduction
import Pell.UniformBalancedScaleAbsorption
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Explicit dyadic scale-count bounds for the main3 balanced range

The finite balanced box decompositions retain four binary scale counts.  This
file bounds each count by a real logarithm, specializes the two source and two
target heights occurring in the manuscript, and packages their product as an
explicit polynomial in `theta` and `1 + log (2Y)`.

No box-counting or sieve estimate is introduced here.
-/

namespace PellPaper

open Filter

noncomputable section

/-- A binary ceiling logarithm is at most one plus twice the natural
logarithm of its positive argument.  The factor two is the elementary bound
`1 / log 2 <= 2`. -/
theorem dyadicScaleCount_cast_le_one_add_two_mul_log_add_one (H : ℕ) :
    (dyadicScaleCount H : ℝ) ≤
      1 + 2 * Real.log ((H + 1 : ℕ) : ℝ) := by
  have harg : (1 : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le H)
  have hlogb0 :
      0 ≤ Real.logb (2 : ℝ) ((H + 1 : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) harg
  have hceil :
      ((⌈Real.logb (2 : ℝ) ((H + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) <
        Real.logb (2 : ℝ) ((H + 1 : ℕ) : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlogb0
  have hclog :
      (Nat.clog 2 (H + 1) : ℝ) <
        Real.logb (2 : ℝ) ((H + 1 : ℕ) : ℝ) + 1 := by
    have heq := Real.natCeil_logb_natCast 2 (H + 1)
    norm_num at heq hceil
    rw [heq] at hceil
    simpa only [Nat.cast_add, Nat.cast_one] using hceil
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9 |>.le
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogarg0 : 0 ≤ Real.log (((H + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg harg
  have hlogb :
      Real.logb (2 : ℝ) ((H + 1 : ℕ) : ℝ) ≤
        2 * Real.log ((H + 1 : ℕ) : ℝ) := by
    rw [Real.logb]
    apply (div_le_iff₀ hlog2pos).2
    nlinarith
  change (Nat.clog 2 (H + 1) : ℝ) ≤ _
  linarith

/-- The two target-coordinate scale counts at height `2Y` cost at most a
fixed logarithmic factor. -/
theorem dyadicScaleCount_two_mul_cast_le
    (Y : ℕ) (hY : 2 ≤ Y) :
    (dyadicScaleCount (2 * Y) : ℝ) ≤
      4 * (1 + Real.log ((2 * Y : ℕ) : ℝ)) := by
  let x : ℝ := ((2 * Y : ℕ) : ℝ)
  have hx : (4 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.mul_le_mul_left 2 hY
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hprod : 0 ≤ x * (x - 2) :=
    mul_nonneg hxpos.le (sub_nonneg.mpr (by linarith))
  have hargSq : (((2 * Y + 1 : ℕ) : ℝ)) ≤ x ^ 2 := by
    have hcast : (((2 * Y + 1 : ℕ) : ℝ)) = x + 1 := by
      simp [x]
    rw [hcast]
    nlinarith
  have hlogArg :
      Real.log (((2 * Y + 1 : ℕ) : ℝ)) ≤
        2 * Real.log x := by
    calc
      Real.log (((2 * Y + 1 : ℕ) : ℝ)) ≤ Real.log (x ^ 2) :=
        Real.log_le_log (by positivity) hargSq
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hscale :=
    dyadicScaleCount_cast_le_one_add_two_mul_log_add_one (2 * Y)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  change (dyadicScaleCount (2 * Y) : ℝ) ≤
    4 * (1 + Real.log x)
  linarith

/-- The source-coordinate scale count at the literal ceiling height
`ceil((2Y)^(theta+1/4))` is at most an explicit linear-logarithmic factor. -/
theorem dyadicScaleCount_main3FactorHeight_cast_le
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) : ℝ) ≤
      4 * (theta + 1) *
        (1 + Real.log ((2 * Y : ℕ) : ℝ)) := by
  let x : ℝ := ((2 * Y : ℕ) : ℝ)
  let a : ℝ := theta + 1 / 4
  let z : ℝ := x ^ a
  let H : ℕ := dyadicFactorHeight (theta + 1 / 4) Y
  have hx : (4 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.mul_le_mul_left 2 hY
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have haone : (1 : ℝ) ≤ a := by dsimp [a]; linarith
  have hzpos : 0 < z := by
    dsimp [z]
    exact Real.rpow_pos_of_pos hxpos _
  have hzfour : (4 : ℝ) ≤ z := by
    calc
      (4 : ℝ) ≤ x := hx
      _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hxone haone
      _ = z := rfl
  have hceil : (H : ℝ) < z + 1 := by
    dsimp [H, dyadicFactorHeight, z, x, a]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have hzQuadratic : 0 ≤ (z - 2) * (z + 1) :=
    mul_nonneg (sub_nonneg.mpr (by linarith)) (by linarith)
  have hHplusSq : (((H + 1 : ℕ) : ℝ)) ≤ z ^ 2 := by
    push_cast
    nlinarith
  have hlogH :
      Real.log (((H + 1 : ℕ) : ℝ)) ≤
        2 * a * Real.log x := by
    calc
      Real.log (((H + 1 : ℕ) : ℝ)) ≤ Real.log (z ^ 2) :=
        Real.log_le_log (by positivity) hHplusSq
      _ = 2 * Real.log z := by rw [Real.log_pow]; norm_num
      _ = 2 * a * Real.log x := by
        rw [show Real.log z = a * Real.log x by
          dsimp [z]
          exact Real.log_rpow hxpos a]
        ring
  have hscale := dyadicScaleCount_cast_le_one_add_two_mul_log_add_one H
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have haUpper : a ≤ theta + 1 := by dsimp [a]; norm_num
  have haLog : a * Real.log x ≤ (theta + 1) * Real.log x :=
    mul_le_mul_of_nonneg_right haUpper hlog0
  change (dyadicScaleCount H : ℝ) ≤
    4 * (theta + 1) * (1 + Real.log x)
  nlinarith

/-- The exact four-coordinate scale-count product retained by both balanced
box sums. -/
noncomputable def main3BalancedDyadicScaleProduct (theta : ℝ) (Y : ℕ) : ℕ :=
  dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
    (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
      (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y)))

/-- Explicit polynomial-logarithmic bound for the full four-coordinate
dyadic scale product used by both balanced box sums. -/
theorem main3Balanced_dyadicScaleProduct_cast_le
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (main3BalancedDyadicScaleProduct theta Y : ℝ) ≤
      256 * (theta + 1) ^ 2 *
        (1 + Real.log ((2 * Y : ℕ) : ℝ)) ^ 4 := by
  let S : ℝ :=
    (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) : ℝ)
  let T : ℝ := (dyadicScaleCount (2 * Y) : ℝ)
  let L : ℝ := 1 + Real.log ((2 * Y : ℕ) : ℝ)
  have hS := dyadicScaleCount_main3FactorHeight_cast_le theta Y htheta hY
  have hT := dyadicScaleCount_two_mul_cast_le Y hY
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hthetaOne0 : 0 ≤ theta + 1 := by linarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have : 0 ≤ Real.log (((2 * Y : ℕ) : ℝ)) :=
      Real.log_natCast_nonneg _
    linarith
  have hpoly :
      S * (S * (T * T)) ≤ 256 * (theta + 1) ^ 2 * L ^ 4 := by
    calc
    S * (S * (T * T)) ≤
        (4 * (theta + 1) * L) *
          ((4 * (theta + 1) * L) * ((4 * L) * (4 * L))) := by
      gcongr
    _ = 256 * (theta + 1) ^ 2 * L ^ 4 := by ring
  simpa [main3BalancedDyadicScaleProduct, S, T, L] using hpoly

/-- The explicit scale-count polynomial is uniformly absorbed by the moving
power `Z^(kappa/theta^2)` throughout the main3 admissible range.  The same
safe smallness condition `10*c^2 <= kappa` used elsewhere in the balanced
route leaves four powers of `log Z` beyond the degree-six polynomial here. -/
theorem eventually_uniform_main3Balanced_dyadicScalePolynomial_le_rpow
    (c kappa : ℝ)
    (hc : 0 < c) (hkappa : 0 < kappa)
    (hsmall : 10 * c ^ 2 ≤ kappa) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log Z / Real.log (Real.log Z)) →
        256 * (theta + 1) ^ 2 *
            (1 + Real.log (2 * Z)) ^ 4 ≤
          Z ^ (kappa / theta ^ 2) := by
  let A : ℝ := 82944 * c ^ 2
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
  have hthetaPlusLe : theta + 1 ≤ 2 * c * Real.log Z := by
    calc
      theta + 1 ≤ 2 * theta := by linarith
      _ ≤ 2 * (c * Real.log Z) :=
        mul_le_mul_of_nonneg_left hthetaLe (by norm_num)
      _ = 2 * c * Real.log Z := by ring
  have hlogProduct :
      1 + Real.log (2 * Z) ≤ 3 * Real.log Z := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
    nlinarith [Real.log_two_lt_d9.le]
  have hthetaPlus0 : 0 ≤ theta + 1 := by linarith
  have hthetaPlusUpper0 : 0 ≤ 2 * c * Real.log Z := by positivity
  have hlogProduct0 : 0 ≤ 1 + Real.log (2 * Z) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
    have hlogtwo0 : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    linarith
  have hthreeLog0 : 0 ≤ 3 * Real.log Z := by positivity
  have hpoly :
      256 * (theta + 1) ^ 2 * (1 + Real.log (2 * Z)) ^ 4 ≤
        A * (Real.log Z) ^ 6 := by
    calc
      256 * (theta + 1) ^ 2 * (1 + Real.log (2 * Z)) ^ 4 ≤
          256 * (2 * c * Real.log Z) ^ 2 *
            (3 * Real.log Z) ^ 4 := by
        gcongr
      _ = A * (Real.log Z) ^ 6 := by
        dsimp [A]
        ring
  have hlogSevenTen : (Real.log Z) ^ 7 ≤ (Real.log Z) ^ 10 := by
    calc
      (Real.log Z) ^ 7 = (Real.log Z) ^ 7 * 1 := by ring
      _ ≤ (Real.log Z) ^ 7 * (Real.log Z) ^ 3 := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hlogone)
          (pow_nonneg hlogpos.le _)
      _ = (Real.log Z) ^ 10 := by ring
  calc
    256 * (theta + 1) ^ 2 * (1 + Real.log (2 * Z)) ^ 4 ≤
        A * (Real.log Z) ^ 6 := hpoly
    _ ≤ Real.log Z * (Real.log Z) ^ 6 :=
      mul_le_mul_of_nonneg_right hAleLog (pow_nonneg hlogpos.le _)
    _ = (Real.log Z) ^ 7 := by ring
    _ ≤ (Real.log Z) ^ 10 := hlogSevenTen
    _ ≤ Z ^ (kappa / theta ^ 2) := hrpowLower

/-- Natural-scale specialization of the uniform absorption theorem. -/
theorem eventually_main3Balanced_dyadicScaleProduct_cast_le_rpow
    (c kappa : ℝ)
    (hc : 0 < c) (hkappa : 0 < kappa)
    (hsmall : 10 * c ^ 2 ≤ kappa) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        (main3BalancedDyadicScaleProduct theta Y : ℝ) ≤
          (Y : ℝ) ^ (kappa / theta ^ 2) := by
  have hreal :=
    eventually_uniform_main3Balanced_dyadicScalePolynomial_le_rpow
      c kappa hc hkappa hsmall
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop 2] with Y hYpoly hY
  intro theta htheta hadmissible
  calc
    (main3BalancedDyadicScaleProduct theta Y : ℝ) ≤
        256 * (theta + 1) ^ 2 *
          (1 + Real.log ((2 * Y : ℕ) : ℝ)) ^ 4 :=
      main3Balanced_dyadicScaleProduct_cast_le theta Y htheta hY
    _ ≤ (Y : ℝ) ^ (kappa / theta ^ 2) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        hYpoly theta htheta hadmissible

/-- The precise fourfold scale-count cost can be absorbed directly into the
elementary low-`DE` envelope.  Under the main3 smallness assumption, the
result retains the explicit saving `1/(200*theta^2)`. -/
theorem eventually_main3Balanced_dyadicScaleProduct_mul_lowDEEnvelope_le
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        (main3BalancedDyadicScaleProduct theta Y : ℝ) *
            (4 * (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) +
              28 * Real.sqrt (Y : ℝ)) ≤
          32 * (Y : ℝ) ^ (1 - 1 / (200 * theta ^ 2)) := by
  have habsorb :=
    eventually_main3Balanced_dyadicScaleProduct_cast_le_rpow
      c ((1 : ℝ) / 400) hc (by norm_num) hsmall
  filter_upwards [habsorb, eventually_ge_atTop 2] with Y hscale hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let K : ℝ := main3BalancedDyadicScaleProduct theta Y
  let q : ℝ := ((1 : ℝ) / 400) / theta ^ 2
  let a : ℝ := 1 - 1 / (100 * theta ^ 2)
  let b : ℝ := 1 - 1 / (200 * theta ^ 2)
  have hyTwo : (2 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast hY
  have hypos : 0 < y := by linarith
  have hyone : 1 ≤ y := by linarith
  have hthetaPos : 0 < theta := by linarith
  have hthetaNe : theta ≠ 0 := hthetaPos.ne'
  have hscale' : K ≤ y ^ q := by
    simpa only [K, y, q] using hscale theta htheta hadmissible
  have hexponentFirst : q + a ≤ b := by
    dsimp [q, a, b]
    field_simp
    nlinarith [sq_pos_of_pos hthetaPos]
  have hexponentSecond : q + 1 / 2 ≤ b := by
    dsimp [q, b]
    field_simp
    nlinarith [sq_pos_of_pos hthetaPos]
  have hfirstPower : y ^ q * y ^ a ≤ y ^ b := by
    rw [← Real.rpow_add hypos]
    exact Real.rpow_le_rpow_of_exponent_le hyone hexponentFirst
  have hsecondPower : y ^ q * Real.sqrt y ≤ y ^ b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hypos]
    exact Real.rpow_le_rpow_of_exponent_le hyone hexponentSecond
  have hfirst : K * y ^ a ≤ y ^ b := by
    exact (mul_le_mul_of_nonneg_right hscale'
      (Real.rpow_nonneg hypos.le _)).trans hfirstPower
  have hsecond : K * Real.sqrt y ≤ y ^ b := by
    exact (mul_le_mul_of_nonneg_right hscale'
      (Real.sqrt_nonneg _)).trans hsecondPower
  change K * (4 * y ^ a + 28 * Real.sqrt y) ≤ 32 * y ^ b
  calc
    K * (4 * y ^ a + 28 * Real.sqrt y) =
        4 * (K * y ^ a) + 28 * (K * Real.sqrt y) := by ring
    _ ≤ 4 * y ^ b + 28 * y ^ b := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = 32 * y ^ b := by ring

end

end PellPaper
