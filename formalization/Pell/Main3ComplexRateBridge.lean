import Pell.Main3ComplexLocalizationFanCharge
import Pell.Main3LargeAnalyticDeterminantGain
import Pell.Main3LargeAnalyticMeshErrorAbsorption
import Pell.TwoLayerFanIndex
import Mathlib.Tactic

namespace PellPaper

noncomputable section

/-- The shift-dependent logarithmic coefficient after adding the sharp
radial/discriminant and positive-fan localization charges. -/
def main3ComplexCombinedShiftLogCoefficient (B : ℕ) : ℝ :=
  (B : ℝ) * ((B : ℝ) + 2) / 2

/-- Fixed logarithmic constant in the sharp radial/discriminant ledger after
`C₀ ≤ 32 sqrt |a|`, `r, ell ≥ 1`, and the dyadic endpoint comparisons. -/
def main3ComplexRadialFixedLogCost (B : ℕ) : ℝ :=
  ((B : ℝ) + 1) * Real.log 64 +
    (B : ℝ) * ((B : ℝ) + 1) * Real.log 2048

/-- Fixed terms left after the scale-dependent radial cost, localization
loss, and kappa-charge have been separated. -/
def main3ComplexRateFixedLogCost (B : ℕ) (radialFixedCost : ℝ) : ℝ :=
  radialFixedCost +
    main3ComplexLocalizationFixedFanCost B +
    main3ComplexCombinedShiftLogCoefficient B * Real.log 2 +
    dyadicEndpointDoublingLogCost 1 B +
    Real.log (Nat.factorial
      (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
    twoLayerFanTaylorTail B *
      (Fintype.card (generalBidegreeGrid 1 B) : ℝ)

/-- A convenient rigorous rational upper bound for `log 2`. -/
theorem log_two_le_three_div_four :
    Real.log 2 ≤ (3 / 4 : ℝ) := by
  have hpow : (2 : ℝ) ≤ (9 / 8 : ℝ) ^ (6 : ℕ) := by norm_num
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hpow
  rw [Real.log_pow] at hlog
  have hsmall := Real.log_le_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 9 / 8)
  norm_num at hsmall
  nlinarith

/-- A convenient rigorous rational upper bound for `log 3`. -/
theorem log_three_le_six_div_five :
    Real.log 3 ≤ (6 / 5 : ℝ) := by
  have hpow : (3 : ℝ) ≤ (16 / 15 : ℝ) ^ (18 : ℕ) := by norm_num
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hpow
  rw [Real.log_pow] at hlog
  have hsmall := Real.log_le_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 16 / 15)
  norm_num at hsmall
  nlinarith

/-- The complete fixed complex ledger is at most `30(B+1)^2`.  This includes
the radial constants, positive-fan localization constants, shift-window
constant, endpoint doubling, factorial, and Taylor tail. -/
theorem main3ComplexRateFixedLogCost_le_thirty_mul_sq (B : ℕ) :
    main3ComplexRateFixedLogCost B (main3ComplexRadialFixedLogCost B) ≤
      30 * ((B : ℝ) + 1) ^ 2 := by
  let b : ℝ := B
  let n : ℕ := 2 * (B + 1)
  have hb0 : 0 ≤ b := by positivity
  have hb1 : 1 ≤ b + 1 := by
    dsimp [b]
    have h : (0 : ℝ) ≤ B := by positivity
    linarith
  have hlog2 := log_two_le_three_div_four
  have hlog3 := log_three_le_six_div_five
  have hlog64 : Real.log 64 ≤ (9 / 2 : ℝ) := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hlog2048 : Real.log 2048 ≤ (33 / 4 : ℝ) := by
    rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hlog12 : Real.log 12 ≤ (27 / 10 : ℝ) := by
    rw [show (12 : ℝ) = 3 * 2 ^ (2 : ℕ) by norm_num,
      Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ^ (2 : ℕ) ≠ 0), Real.log_pow]
    norm_num
    nlinarith
  have hlog4 : Real.log 4 ≤ (3 / 2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have hfacNat : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfacReal : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hfacNat
  have hlogFacPow : Real.log (n.factorial : ℝ) ≤
      Real.log ((n : ℝ) ^ n) := by
    exact Real.log_le_log (by positivity) hfacReal
  have hlogFac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Real.log_pow] at hlogFacPow
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) :=
      Real.log_le_self (by positivity)
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hsource :
      1 * ((1 + 1) * (B + 1)) / 2 = B + 1 := by omega
  have htarget :
      B * ((1 + 1) * (B + 1)) / 2 = B * (B + 1) := by
    calc
      B * ((1 + 1) * (B + 1)) / 2 =
          (B * (B + 1)) * 2 / 2 := by
        congr 1
        ring
      _ = B * (B + 1) :=
        Nat.mul_div_left _ (by norm_num : 0 < 2)
  have hcard :
      Fintype.card (generalBidegreeGrid 1 B) = 2 * (B + 1) := by
    calc
      Fintype.card (generalBidegreeGrid 1 B) =
          (generalBidegreeGrid 1 B).card := Fintype.card_coe _
      _ = (1 + 1) * (B + 1) := card_generalBidegreeGrid 1 B
      _ = 2 * (B + 1) := by omega
  unfold main3ComplexRateFixedLogCost main3ComplexRadialFixedLogCost
    main3ComplexLocalizationFixedFanCost
    main3ComplexCombinedShiftLogCoefficient
    dyadicEndpointDoublingLogCost twoLayerFanTaylorTail
  rw [hsource, htarget, hcard]
  push_cast
  dsimp [b, n] at hb0 hb1 hlogFac ⊢
  norm_num at hlogFac
  nlinarith [mul_nonneg hb0 hb0]

/-- The single explicit growth hypothesis `exp (800 theta^2) < Y` absorbs
the entire fixed complex ledger at the surviving `theta^2/16` gain. -/
theorem main3ComplexRateFixedLogCost_lt_theta_sq_div_sixteen_mul_log
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    main3ComplexRateFixedLogCost (main3BalancedDegree theta)
        (main3ComplexRadialFixedLogCost (main3BalancedDegree theta)) <
      theta ^ 2 / 16 * Real.log (Y : ℝ) := by
  let t : ℝ := theta ^ 2
  let B : ℕ := main3BalancedDegree theta
  have ht9 : 9 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg (theta - 3)]
  have hYpos : (0 : ℝ) < Y := (Real.exp_pos _).trans hYgrow
  have hlog : 800 * t < Real.log (Y : ℝ) := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hYpos hYgrow
    rw [Real.log_exp] at h
    simpa only [t] using h
  have hBupper : (B : ℝ) < t + 1 := by
    dsimp [B, t]
    exact (main3UnbalancedDegree_nearSquare theta).2
  have hBplus : (B : ℝ) + 1 < t + 2 := by linarith
  have hsq : ((B : ℝ) + 1) ^ 2 < (t + 2) ^ 2 := by
    exact (sq_lt_sq₀ (by positivity) (by positivity)).2 hBplus
  have hpoly : 30 * (t + 2) ^ 2 ≤ 50 * t ^ 2 := by
    have haux : 0 ≤ (t - 9) * (t + 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hlogGain : 50 * t ^ 2 < t / 16 * Real.log (Y : ℝ) := by
    have hscale := mul_lt_mul_of_pos_left hlog (by positivity : 0 < t / 16)
    nlinarith
  have hcost := main3ComplexRateFixedLogCost_le_thirty_mul_sq B
  dsimp [B, t] at hcost hsq hpoly hlogGain ⊢
  exact hcost.trans_lt
    (((mul_lt_mul_of_pos_left hsq (by norm_num : (0 : ℝ) < 30)).trans_le
      hpoly).trans hlogGain)

/-- The two separately arising coefficients of `log |a|` add to the
manuscript coefficient `B(B+2)/2`. -/
theorem main3Complex_radial_add_localization_shift_charge_eq
    (B : ℕ) (x : ℝ) :
    ((B : ℝ) * ((B : ℝ) + 1) / 2) * x +
        ((B : ℝ) / 2) * x =
      main3ComplexCombinedShiftLogCoefficient B * x := by
  unfold main3ComplexCombinedShiftLogCoefficient
  ring

/-- The actual main3 shift window turns the combined `log |a|` term into
the exact kappa charge plus the one fixed `log 2` term. -/
theorem main3Complex_combinedShiftLog_le_discriminantCharge_add_fixed
    (B : ℕ) (theta : ℝ) (Y : ℕ) (a : ℤ)
    (htheta : 3 ≤ theta) (hY : 1 ≤ Y) (ha : a ≠ 0)
    (hshift : |(a : ℝ)| ≤
      2 * (Y : ℝ) ^ main3BalancedRExponent theta) :
    main3ComplexCombinedShiftLogCoefficient B * Real.log |(a : ℝ)| ≤
      main3LargeAnalyticDiscriminantCharge B theta * Real.log (Y : ℝ) +
        main3ComplexCombinedShiftLogCoefficient B * Real.log 2 := by
  have haReal : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have habspos : 0 < |(a : ℝ)| := abs_pos.mpr haReal
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hrpowpos : 0 < (Y : ℝ) ^ main3BalancedRExponent theta :=
    Real.rpow_pos_of_pos hYpos _
  have hupperpos : 0 < 2 * (Y : ℝ) ^ main3BalancedRExponent theta := by
    positivity
  have hlog := Real.log_le_log habspos hshift
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hrpowpos.ne',
    Real.log_rpow hYpos] at hlog
  have hcoef0 : 0 ≤ main3ComplexCombinedShiftLogCoefficient B := by
    unfold main3ComplexCombinedShiftLogCoefficient
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hcoef0
  have hthetaSq : theta ^ 2 ≠ 0 := by positivity
  have hcharge :
      main3ComplexCombinedShiftLogCoefficient B *
          main3BalancedRExponent theta =
        main3LargeAnalyticDiscriminantCharge B theta := by
    unfold main3ComplexCombinedShiftLogCoefficient
      main3BalancedRExponent main3LargeAnalyticDiscriminantCharge
    field_simp [hthetaSq]
  rw [mul_add, ← mul_assoc, hcharge] at hscaled
  linarith

/-- Nonemptiness of an actual large-analytic block plus the sharp mesh error
absorption improves the rowwise `n` bound to an endpoint inequality. -/
theorem main3LargeAnalytic_four_mul_mesh_sqrt_shift_lt_endpoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    4 * (main3UnbalancedM theta Y : ℝ) *
        Real.sqrt |(shiftedSquareA h v : ℝ)| < (N : ℝ) := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  obtain ⟨⟨d, w, n⟩, hp⟩ :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_block_nonempty hcell
  have hmesh :=
    main3LargeAnalytic_unbalancedMesh_mul_sqrt_shift_le_n
      htheta hY hi hp
  have hnUpperNat : n < 2 * N :=
    (mem_squarefreeShiftedSquareBlock.mp hp).2.2.2.2.2.2.2.2.1
  have hnUpper : (n : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hnUpperNat
  nlinarith

/-- The actual large-analytic endpoint makes the target defect scale strictly
larger than the source cell scale.  This is the lower fan-window input. -/
theorem main3LargeAnalytic_complexSourceLogScale_lt_defectLogScale
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    main3ComplexSourceLogScale (main3UnbalancedM theta Y) <
      main3ComplexDefectLogScale (shiftedSquareA h v) N := by
  let a := shiftedSquareA h v
  let M := main3UnbalancedM theta Y
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have ha : a ≠ 0 := by
    simpa only [a] using
      (nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
        hiBroad hcell).2.2.1
  have haReal : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hsqrt : 0 < Real.sqrt |(a : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.mpr haReal)
  have hMNat : 0 < M := by
    simpa only [M] using
      (main3UnbalancedM_parameter_package theta Y htheta (by omega)).1
  have hM : (0 : ℝ) < M := by exact_mod_cast hMNat
  have hendpoint : 4 * (M : ℝ) * Real.sqrt |(a : ℝ)| < (N : ℝ) := by
    simpa only [M, a] using
      main3LargeAnalytic_four_mul_mesh_sqrt_shift_lt_endpoint htheta hY hi
  have hN : (0 : ℝ) < N :=
    (mul_nonneg (mul_nonneg (by norm_num) hM.le)
      (Real.sqrt_nonneg _)).trans_lt hendpoint
  have hproduct :
      (M : ℝ) * (12 * Real.sqrt |(a : ℝ)|) < (N : ℝ) * 3 := by
    nlinarith
  have hlog := Real.strictMonoOn_log
    (mul_pos hM (by positivity)) (mul_pos hN (by norm_num)) hproduct
  rw [Real.log_mul hM.ne' (by positivity :
      12 * Real.sqrt |(a : ℝ)| ≠ 0),
    Real.log_mul hN.ne' (by norm_num : (3 : ℝ) ≠ 0)] at hlog
  dsimp [main3ComplexSourceLogScale, main3ComplexDefectLogScale, M, a]
  linarith

/-- At the standing explicit base threshold the chart subtraction `log 3`
still leaves at least half of the ambient logarithmic scale. -/
theorem half_log_le_main3ComplexSourceLogScale
    {theta : ℝ} {Y : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y) :
    Real.log (Y : ℝ) / 2 ≤
      main3ComplexSourceLogScale (main3UnbalancedM theta Y) := by
  let M := main3UnbalancedM theta Y
  let m := main3UnbalancedMLogExponent theta Y
  let L := Real.log (Y : ℝ)
  obtain ⟨_hMpos, _hMle, hmlower, _hmupper, _hdefect, hmLog⟩ :=
    main3UnbalancedM_parameter_package theta Y htheta (by omega)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have h81Y : (81 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (show 81 ≤ Y by omega)
  have hlog81 : Real.log (81 : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) h81Y
  have hlog3nonneg : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog81eq : Real.log (81 : ℝ) = 4 * Real.log 3 := by
    rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog81eq] at hlog81
  have hlog3 : Real.log 3 ≤ (35 / 72 : ℝ) * L := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hmlower hLpos.le
  dsimp [m, L] at hmLog hscaled ⊢
  rw [main3ComplexSourceLogScale, ← hmLog]
  nlinarith

/-- An upper exponent bound `log N / log Y ≤ theta` places the exact defect
scale below the final fan wall.  The proof uses the near-square degree and
the preceding half-log lower bound for the chart-corrected source scale. -/
theorem main3ComplexDefectLogScale_le_two_mul_degree_sourceLogScale
    {theta : ℝ} {Y N : ℕ} {a : ℤ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y) (ha : a ≠ 0)
    (hq : Real.log (N : ℝ) / Real.log (Y : ℝ) ≤ theta) :
    main3ComplexDefectLogScale a N ≤
      2 * main3ComplexSourceLogScale (main3UnbalancedM theta Y) *
        (main3BalancedDegree theta : ℝ) := by
  let L := Real.log (Y : ℝ)
  let ellM := main3ComplexSourceLogScale (main3UnbalancedM theta Y)
  let B := main3BalancedDegree theta
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hqL : Real.log (N : ℝ) ≤ theta * L := by
    dsimp [L] at hLpos ⊢
    exact (div_le_iff₀ hLpos).mp hq
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt |(a : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Int.one_le_abs ha)
  have hnumeratorOne : (1 : ℝ) ≤ 12 * Real.sqrt |(a : ℝ)| := by
    nlinarith
  have hdefectLog : main3ComplexDefectLogScale a N ≤ Real.log (N : ℝ) := by
    unfold main3ComplexDefectLogScale
    have := Real.log_nonneg hnumeratorOne
    linarith
  have hhalf : L / 2 ≤ ellM := by
    simpa only [L, ellM] using
      half_log_le_main3ComplexSourceLogScale htheta hY
  have hthetaB : theta ≤ (B : ℝ) := by
    have hnear := main3UnbalancedDegree_nearSquare theta |>.1
    dsimp [B]
    nlinarith [sq_nonneg (theta - 1)]
  have hL0 : 0 ≤ L := hLpos.le
  have hBL : theta * L ≤ (B : ℝ) * L :=
    mul_le_mul_of_nonneg_right hthetaB hL0
  have hBellM : (B : ℝ) * L ≤ 2 * ellM * (B : ℝ) := by
    have hB0 : (0 : ℝ) ≤ B := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hhalf hB0]
  exact hdefectLog.trans (hqL.trans (hBL.trans hBellM))

/-- Exact elementary growth condition that upgrades the enlarged
`theta+1/4` cover to the manuscript endpoint `N ≤ Y^theta`.  It uses the
retained product-height inequality, not merely the coarse cover height. -/
theorem main3LargeAnalytic_endpoint_le_rpow_of_exact_growth
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hgrowth :
      2 * ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) *
          (Y : ℝ) ^ main3BalancedRExponent theta ≤
        (Y : ℝ) ^ (theta + 1 / 2)) :
    (N : ℝ) ≤ (Y : ℝ) ^ theta := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  obtain ⟨⟨d, e, u, v'⟩, hp⟩ := hcell
  obtain ⟨hcond, hvR, _hshift, hvEq, _hdiff, _hDlo, _hDhi,
      hNlo, _hNhi⟩ :=
    mem_admissibleUnbalancedShiftedSquareFibre.mp hp
  subst v'
  obtain ⟨hd, he, _hu, hv, _hdH, _heH, _huY, _hvY, _hsd, _hse,
      _hcop, _hYuv, _huvY, _hvu, _hvsq, _hsign, hheight⟩ := hcond
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hsqrtYpos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  have hRupperNat :=
    (main3BalancedR_parameter_package theta Y htheta (by omega)).2.2.1
  have hRupper :
      (main3BalancedR theta Y : ℝ) ≤
        2 * (Y : ℝ) ^ main3BalancedRExponent theta := by
    exact hRupperNat
  have hvRreal : (v : ℝ) < (main3BalancedR theta Y : ℝ) := by
    exact_mod_cast hvR
  have hvPower :
      (v : ℝ) < 2 * (Y : ℝ) ^ main3BalancedRExponent theta :=
    hvRreal.trans_le hRupper
  have heDevNat : e * v ≤ (d * e) * v := by
    exact Nat.mul_le_mul_right v (Nat.le_mul_of_pos_left e hd)
  have hNdevNat : N ≤ (d * e) * v := hNlo.trans heDevNat
  have hNdev : (N : ℝ) ≤ ((d * e : ℕ) : ℝ) * (v : ℝ) := by
    exact_mod_cast hNdevNat
  have hheightV :
      ((d * e : ℕ) : ℝ) * Real.sqrt (Y : ℝ) * (v : ℝ) ≤
        ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) * (v : ℝ) :=
    mul_le_mul_of_nonneg_right hheight (by positivity)
  have hrightPos :
      0 < ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hvScaled :
      ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) * (v : ℝ) <
        ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) *
          (2 * (Y : ℝ) ^ main3BalancedRExponent theta) :=
    mul_lt_mul_of_pos_left hvPower hrightPos
  have hNsqrt :
      (N : ℝ) * Real.sqrt (Y : ℝ) <
        2 * ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) *
          (Y : ℝ) ^ main3BalancedRExponent theta := by
    calc
      (N : ℝ) * Real.sqrt (Y : ℝ) ≤
          (((d * e : ℕ) : ℝ) * (v : ℝ)) * Real.sqrt (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hNdev (Real.sqrt_nonneg _)
      _ = ((d * e : ℕ) : ℝ) * Real.sqrt (Y : ℝ) * (v : ℝ) := by ring
      _ ≤ ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) * (v : ℝ) := hheightV
      _ < ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) *
          (2 * (Y : ℝ) ^ main3BalancedRExponent theta) := hvScaled
      _ = 2 * ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) *
          (Y : ℝ) ^ main3BalancedRExponent theta := by ring
  have hNpower :
      (N : ℝ) * Real.sqrt (Y : ℝ) < (Y : ℝ) ^ (theta + 1 / 2) :=
    hNsqrt.trans_le hgrowth
  rw [Real.rpow_add hYpos, ← Real.sqrt_eq_rpow] at hNpower
  exact (lt_of_mul_lt_mul_right hNpower hsqrtYpos.le).le

/-- The standard fixed-cost growth threshold is far stronger than the exact
growth condition needed to recover `N ≤ Y^theta` from the enlarged cover. -/
theorem main3LargeAnalytic_exact_endpoint_growth_of_exp_eightHundred
    {theta : ℝ} {Y : ℕ}
    (htheta : 3 ≤ theta)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    2 * ((2 * Y : ℕ) : ℝ) ^ (theta + 1 / 4) *
        (Y : ℝ) ^ main3BalancedRExponent theta ≤
      (Y : ℝ) ^ (theta + 1 / 2) := by
  let y : ℝ := Y
  let delta := main3BalancedRExponent theta
  let L := Real.log y
  have hypos : 0 < y := (Real.exp_pos _).trans hYgrow
  have hL : 800 * theta ^ 2 < L := by
    have hlog := Real.strictMonoOn_log (Real.exp_pos _) hypos hYgrow
    rw [Real.log_exp] at hlog
    simpa only [L] using hlog
  have hthetaSq : 9 ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hdelta : delta ≤ (1 / 900 : ℝ) := by
    dsimp [delta, main3BalancedRExponent]
    have hdenom : 0 < 100 * theta ^ 2 := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith
  have hgap : (1 / 5 : ℝ) ≤ 1 / 4 - delta := by linarith
  have hLpos : 0 < L := by linarith
  have hgapL : (1 / 5 : ℝ) * L ≤ (1 / 4 - delta) * L :=
    mul_le_mul_of_nonneg_right hgap hLpos.le
  have hlog2 : Real.log 2 ≤ (2 : ℝ) :=
    Real.log_le_self (by norm_num)
  have hthetaCoeff : 0 ≤ theta + 5 / 4 := by linarith
  have hlogTerm :
      (theta + 5 / 4) * Real.log 2 ≤ 2 * (theta + 5 / 4) :=
    by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hlog2 hthetaCoeff
  have hpoly : 2 * (theta + 5 / 4) ≤ 160 * theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hscale : 160 * theta ^ 2 < (1 / 5 : ℝ) * L := by
    nlinarith
  have hmain :
      (theta + 5 / 4) * Real.log 2 ≤ (1 / 4 - delta) * L :=
    hlogTerm.trans (hpoly.trans (hscale.le.trans hgapL))
  have hargument :
      Real.log 2 + (Real.log 2 + L) * (theta + 1 / 4) +
          L * delta ≤
        L * (theta + 1 / 2) := by
    calc
      Real.log 2 + (Real.log 2 + L) * (theta + 1 / 4) +
          L * delta =
        (theta + 5 / 4) * Real.log 2 +
          (theta + 1 / 4 + delta) * L := by ring
      _ ≤ (1 / 4 - delta) * L +
          (theta + 1 / 4 + delta) * L :=
        by simpa only [add_comm] using
          add_le_add_right hmain ((theta + 1 / 4 + delta) * L)
      _ = L * (theta + 1 / 2) := by ring
  have htwoYpos : (0 : ℝ) < ((2 * Y : ℕ) : ℝ) := by
    push_cast
    positivity
  push_cast
  change 2 * (2 * y) ^ (theta + 1 / 4) * y ^ delta ≤
    y ^ (theta + 1 / 2)
  rw [Real.rpow_def_of_pos (by positivity : 0 < 2 * y), Real.rpow_def_of_pos hypos,
    Real.rpow_def_of_pos hypos]
  calc
    2 * Real.exp (Real.log (2 * y) * (theta + 1 / 4)) *
          Real.exp (Real.log y * delta) =
        Real.exp (Real.log 2 +
          Real.log (2 * y) * (theta + 1 / 4) +
            Real.log y * delta) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (Real.log y * (theta + 1 / 2)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
      simpa only [L] using hargument

/-- Under the standard determinant fixed-cost threshold, every actual
large-analytic endpoint in the enlarged cover satisfies the manuscript
upper range. -/
theorem main3LargeAnalytic_endpoint_le_rpow
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (N : ℝ) ≤ (Y : ℝ) ^ theta := by
  exact main3LargeAnalytic_endpoint_le_rpow_of_exact_growth
    htheta hY hi
      (main3LargeAnalytic_exact_endpoint_growth_of_exp_eightHundred
        htheta hYgrow)

/-- The endpoint logarithmic exponent of an actual large-analytic block lies
in the exact interval consumed by the main3 charged-surplus theorem. -/
theorem main3LargeAnalytic_endpoint_logExponent_mem
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    0 ≤ Real.log (N : ℝ) / Real.log (Y : ℝ) ∧
      Real.log (N : ℝ) / Real.log (Y : ℝ) ≤ theta := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hNposNat :=
    (nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiBroad hcell).2.1
  have hNoneNat : 1 ≤ N := hNposNat
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hNoneNat)
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  constructor
  · exact div_nonneg hlogN0 hlogYpos.le
  · apply (div_le_iff₀ hlogYpos).2
    have hNpower := main3LargeAnalytic_endpoint_le_rpow
      htheta hY hYgrow hi
    have hlog := Real.log_le_log hNpos hNpower
    rw [Real.log_rpow (by positivity : (0 : ℝ) < Y)] at hlog
    simpa only [mul_comm] using hlog

/-- Every actual positive-shift large-analytic block has a valid fan index
for the chart-corrected complex source and defect scales. -/
theorem exists_main3LargeAnalytic_complexFanIndex
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v) :
    ∃ k : ℕ,
      1 ≤ k ∧ k ≤ main3BalancedDegree theta ∧
      (2 * (k : ℝ) - 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) ≤
        main3ComplexDefectLogScale (shiftedSquareA h v) N ∧
      main3ComplexDefectLogScale (shiftedSquareA h v) N ≤
        (2 * (k : ℝ) + 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) := by
  let ellM := main3ComplexSourceLogScale (main3UnbalancedM theta Y)
  let ellX := main3ComplexDefectLogScale (shiftedSquareA h v) N
  let B := main3BalancedDegree theta
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hellM : 0 < ellM := by
    have hhalf := half_log_le_main3ComplexSourceLogScale htheta hY
    dsimp [ellM]
    linarith
  have hmq : ellM ≤ ellX := by
    simpa only [ellM, ellX] using
      (main3LargeAnalytic_complexSourceLogScale_lt_defectLogScale
        htheta hY hi).le
  have hq :=
    (main3LargeAnalytic_endpoint_logExponent_mem htheta hY hYgrow hi).2
  have hqB : ellX ≤ 2 * ellM * (B : ℝ) := by
    simpa only [ellX, ellM, B] using
      main3ComplexDefectLogScale_le_two_mul_degree_sourceLogScale
        htheta hY ha.ne' hq
  refine ⟨nearestTwoLayerFanIndex ellM ellX, ?_⟩
  simpa only [ellM, ellX, B] using
    nearestTwoLayerFanIndex_spec B ellM ellX hellM hmq hqB

/-- Pure scalar bridge from a sharp radial cost and the positive-fan
localization charge to the exact strict rate required by complex minor
vanishing. -/
theorem main3Complex_rate_of_radial_and_positiveFan_charges
    (B k : ℕ) (theta m q L cost radialFixedCost : ℝ)
    (M N : ℕ) (a : ℤ)
    (hkpos : 1 ≤ k) (hkB : k ≤ B) (ha : a ≠ 0)
    (hL : 0 ≤ L)
    (hlogM : m * L = Real.log (M : ℝ))
    (hlogN : q * L = Real.log (N : ℝ))
    (hradial :
      cost ≤
        twoLayerBalancedDoubledBaseLogCost B q L +
          ((B : ℝ) * ((B : ℝ) + 1) / 2) * Real.log |(a : ℝ)| +
            radialFixedCost)
    (hshiftCharge :
      main3ComplexCombinedShiftLogCoefficient B * Real.log |(a : ℝ)| ≤
        main3LargeAnalyticDiscriminantCharge B theta * L +
          main3ComplexCombinedShiftLogCoefficient B * Real.log 2)
    (hgain :
      theta ^ 2 / 16 ≤
        twoLayerBalancedFanSurplus B k m q -
          main3LargeAnalyticDiscriminantCharge B theta)
    (hfixed :
      main3ComplexRateFixedLogCost B radialFixedCost <
        theta ^ 2 / 16 * L) :
    cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
      twoLayerFanTaylorTail B *
        (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k
        (main3ComplexSourceLogScale M)
        (main3ComplexDefectLogScale a N) := by
  have hlocal := twoLayerWeight_sub_main3ComplexPositiveFanCharge_le
    B k M N a hkpos hkB ha
  have hraw :
      twoLayerWeight B k (Real.log (M : ℝ)) (Real.log (N : ℝ)) =
        twoLayerWeight B k (m * L) (q * L) := by
    rw [hlogM, hlogN]
  have hbalance :=
    twoLayerWeight_sub_twoLayerBalancedDoubledBaseLogCost_eq
      B k m q L hkB
  have hgainL := mul_le_mul_of_nonneg_right hgain hL
  rw [hraw] at hlocal
  have hcombined :=
    main3Complex_radial_add_localization_shift_charge_eq
      B (Real.log |(a : ℝ)|)
  unfold main3ComplexRateFixedLogCost at hfixed
  linarith

/-- Concrete capstone for an actual positive-shift large-analytic block.
Once the sharp radial/discriminant logarithmic ledger is supplied, it chooses
the fan index, proves both literal chart-corrected fan walls, and proves the
exact strict rate consumed by complex minor vanishing. -/
theorem exists_main3LargeAnalytic_complexFanIndex_and_rate_of_radialLedger
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v) (cost : ℝ)
    (hradial :
      cost ≤
        twoLayerBalancedDoubledBaseLogCost
            (main3BalancedDegree theta)
            (Real.log (N : ℝ) / Real.log (Y : ℝ))
            (Real.log (Y : ℝ)) +
          ((main3BalancedDegree theta : ℝ) *
              ((main3BalancedDegree theta : ℝ) + 1) / 2) *
            Real.log |(shiftedSquareA h v : ℝ)| +
          main3ComplexRadialFixedLogCost
            (main3BalancedDegree theta)) :
    ∃ k : ℕ,
      1 ≤ k ∧ k ≤ main3BalancedDegree theta ∧
      (2 * (k : ℝ) - 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) ≤
        main3ComplexDefectLogScale (shiftedSquareA h v) N ∧
      main3ComplexDefectLogScale (shiftedSquareA h v) N ≤
        (2 * (k : ℝ) + 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) ∧
      cost +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1
              (main3BalancedDegree theta))) : ℝ) +
        twoLayerFanTaylorTail (main3BalancedDegree theta) *
          (Fintype.card (generalBidegreeGrid 1
            (main3BalancedDegree theta)) : ℝ) <
        twoLayerWeight (main3BalancedDegree theta) k
          (main3ComplexSourceLogScale (main3UnbalancedM theta Y))
          (main3ComplexDefectLogScale (shiftedSquareA h v) N) := by
  let B := main3BalancedDegree theta
  let M := main3UnbalancedM theta Y
  let a := shiftedSquareA h v
  let m := main3UnbalancedMLogExponent theta Y
  let q := Real.log (N : ℝ) / Real.log (Y : ℝ)
  let L := Real.log (Y : ℝ)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hq :=
    main3LargeAnalytic_endpoint_logExponent_mem htheta hY hYgrow hi
  obtain ⟨k, hkpos, hkB, hfanLower, hfanUpper⟩ :=
    exists_main3LargeAnalytic_complexFanIndex htheta hY hYgrow hi ha
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiBroad :=
    (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1).1
  have hshift : |(a : ℝ)| ≤
      2 * (Y : ℝ) ^ main3BalancedRExponent theta := by
    dsimp [a]
    exact (main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
      htheta (by omega : 2 ≤ Y) hiBroad).2.1.le
  have hshiftCharge :=
    main3Complex_combinedShiftLog_le_discriminantCharge_add_fixed
      B theta Y a htheta (by omega) (by omega) hshift
  have hgain :=
    theta_sq_div_sixteen_le_main3LargeAnalytic_ceilingChargedFanSurplus
      theta Y k q htheta (by omega) (by simpa only [q] using hq.1)
        (by simpa only [q] using hq.2)
  have hlogM : m * L = Real.log (M : ℝ) := by
    simpa only [m, L, M] using
      (main3UnbalancedM_parameter_package theta Y htheta (by omega)).2.2.2.2.2
  have hlogN : q * L = Real.log (N : ℝ) := by
    dsimp [q, L]
    exact div_mul_cancel₀ _ hLpos.ne'
  have hfixed :=
    main3ComplexRateFixedLogCost_lt_theta_sq_div_sixteen_mul_log
      theta Y htheta hYgrow
  have hrate := main3Complex_rate_of_radial_and_positiveFan_charges
    B k theta m q L cost (main3ComplexRadialFixedLogCost B)
      M N a hkpos hkB (by omega) hLpos.le hlogM hlogN
      (by simpa only [B, q, L, a] using hradial)
      hshiftCharge hgain (by simpa only [B, L] using hfixed)
  refine ⟨k, hkpos, hkB, ?_, ?_, ?_⟩
  · simpa only [B, M, a] using hfanLower
  · simpa only [B, M, a] using hfanUpper
  · simpa only [B, M, a] using hrate

end

end PellPaper
