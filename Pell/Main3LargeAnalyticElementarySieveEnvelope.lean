import Pell.IntrinsicOddHomogeneousPolynomialSquareSieveElementary
import Pell.Main3LargeAnalyticSieveEnvelopePower
import Pell.Main3LargeAnalyticCoarseKeyEnvelope
import Pell.Main3LargeAnalyticOuterPowerLedger
import Mathlib.Tactic

/-!
# Aggregate and power envelopes for the elementary Main3 sieve

The compatibility degree parameter is deliberately retained but unused.
This lets the large-analytic geometry keep all its current interfaces.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

def fullCellElementarySieveVariableAggregateEnvelope
    (N _D : ℕ) (cellCount area reciprocalSum : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  cellCount *
      ((4608 / Real.log 2) * area * Real.log (N : ℝ) / (N : ℝ) +
        576 * (N : ℝ) ^ 3 * Llog ^ 2) +
    864 * (N : ℝ) * Llog * reciprocalSum

theorem fullCellElementarySieveVariableAggregateEnvelope_le_max_reciprocal
    (N D : ℕ) (cellCount area reciprocalSum : ℝ) (hN : 4 ≤ N) :
    fullCellElementarySieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum ≤
      fullCellElementarySieveVariableAggregateEnvelope
        N D cellCount area (max 0 reciprocalSum) := by
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [sq_nonneg (N : ℝ)]
  have hLlog : 0 ≤ Llog := by
    dsimp only [Llog]
    linarith [Real.log_nonneg harg]
  have hcoefficient : 0 ≤ 864 * (N : ℝ) * Llog := by positivity
  unfold fullCellElementarySieveVariableAggregateEnvelope
  dsimp only
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (le_max_right 0 reciprocalSum) hcoefficient)

theorem sum_fullCellElementarySieveEnvelope_le_variableAggregate
    {ι : Type*} (J : Finset ι) (N D : ℕ)
    (degree : ι → ℕ) (U V M mu : ι → ℝ)
    (cellCount area reciprocalSum : ℝ)
    (hN : 4 ≤ N)
    (_hdegree : ∀ i ∈ J, degree i ≤ D)
    (_hmu : ∀ i ∈ J, 0 < mu i)
    (hcellCount : (J.card : ℝ) ≤ cellCount)
    (harea : 0 ≤ area)
    (hareaBound : ∀ i ∈ J, U i * V i / M i ≤ area)
    (hreciprocal : (∑ i ∈ J, 1 / mu i) ≤ reciprocalSum) :
    (∑ i ∈ J,
      fullCellElementarySieveEnvelope N (degree i) (U i) (V i) (M i)
        (mu i)) ≤
      fullCellElementarySieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum := by
  classical
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * area * Real.log (N : ℝ) / (N : ℝ) +
      576 * (N : ℝ) ^ 3 * Llog ^ 2
  let reciprocalCoefficient : ℝ := 864 * (N : ℝ) * Llog
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : 0 ≤ Llog := by
    dsimp [Llog]
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hareaCoefficient :
      0 ≤ (4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ) := by
    positivity
  have hcommon : 0 ≤ common := by
    dsimp [common]
    positivity
  have hreciprocalCoefficient : 0 ≤ reciprocalCoefficient := by
    dsimp [reciprocalCoefficient]
    positivity
  have hpointwise : ∀ i ∈ J,
      fullCellElementarySieveEnvelope N (degree i) (U i) (V i) (M i)
          (mu i) ≤ common + reciprocalCoefficient / mu i := by
    intro i hi
    have hareaTerm :
        (4608 / Real.log 2) * (U i * V i / M i) *
              Real.log (N : ℝ) / (N : ℝ) ≤
          (4608 / Real.log 2) * area *
              Real.log (N : ℝ) / (N : ℝ) := by
      calc
        _ = ((4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
              (U i * V i / M i) := by ring
        _ ≤ ((4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
              area := mul_le_mul_of_nonneg_left (hareaBound i hi) hareaCoefficient
        _ = _ := by ring
    rw [fullCellElementarySieveEnvelope]
    dsimp [common, reciprocalCoefficient, Llog]
    linarith
  calc
    (∑ i ∈ J,
        fullCellElementarySieveEnvelope N (degree i) (U i) (V i) (M i)
          (mu i)) ≤
        ∑ i ∈ J, (common + reciprocalCoefficient / mu i) :=
      Finset.sum_le_sum hpointwise
    _ = (J.card : ℝ) * common +
        reciprocalCoefficient * (∑ i ∈ J, 1 / mu i) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ cellCount * common + reciprocalCoefficient * reciprocalSum := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcellCount hcommon)
        (mul_le_mul_of_nonneg_left hreciprocal hreciprocalCoefficient)
    _ = fullCellElementarySieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum := by rfl

def fullCellElementarySievePowerAggregateEnvelope
    (Z L : ℝ) (_D : ℕ) (cellCount area reciprocalSum : ℝ) : ℝ :=
  cellCount * (9216 * area * L / Z + 4608 * Z ^ 3 * L ^ 2) +
    1728 * Z * L * reciprocalSum

theorem fullCellElementarySieveVariableAggregateEnvelope_le_powerAggregate
    (N D : ℕ) (Z L cellCount area reciprocalSum : ℝ)
    (hN : 4 ≤ N) (hZ : 0 < Z)
    (hZN : Z ≤ (N : ℝ)) (hNZ : (N : ℝ) ≤ 2 * Z)
    (hL : 0 ≤ L)
    (hlogN : Real.log (N : ℝ) ≤ L)
    (hlargeLog : 1 + Real.log (16 * (N : ℝ) ^ 2) ≤ L)
    (hcellCount : 0 ≤ cellCount) (harea : 0 ≤ area)
    (hreciprocal : 0 ≤ reciprocalSum) :
    fullCellElementarySieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum ≤
      fullCellElementarySievePowerAggregateEnvelope
        Z L D cellCount area reciprocalSum := by
  let n : ℝ := N
  let Llog : ℝ := 1 + Real.log (16 * n ^ 2)
  have hn : 0 < n := by dsimp [n]; positivity
  have hlogN0 : 0 ≤ Real.log n := Real.log_nonneg (by
    dsimp [n]
    exact_mod_cast (show 1 ≤ N by omega))
  have hLlog0 : 0 ≤ Llog := by
    dsimp [Llog, n]
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoefficient : 4608 / Real.log 2 ≤ (9216 : ℝ) := by
    apply (div_le_iff₀ hlogTwoPos).2
    nlinarith [show (1 / 2 : ℝ) ≤ Real.log 2 from
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9 |>.le]
  have hinv : 1 / n ≤ 1 / Z :=
    one_div_le_one_div_of_le hZ (by simpa only [n] using hZN)
  have hareaTerm :
      (4608 / Real.log 2) * area * Real.log n / n ≤
        9216 * area * L / Z := by
    calc
      _ = ((4608 / Real.log 2) * area * Real.log n) * (1 / n) := by ring
      _ ≤ (9216 * area * L) * (1 / Z) := by gcongr
      _ = _ := by ring
  have hnCube : n ^ 3 ≤ 8 * Z ^ 3 := by
    have hn0 : 0 ≤ n := hn.le
    have h2Z0 : 0 ≤ 2 * Z := by positivity
    calc
      n ^ 3 ≤ (2 * Z) ^ 3 := pow_le_pow_left₀ hn0 hNZ 3
      _ = 8 * Z ^ 3 := by ring
  have hLlogSq : Llog ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ hLlog0 hL).2 (by simpa only [Llog, n] using hlargeLog)
  have hcubicTerm :
      576 * n ^ 3 * Llog ^ 2 ≤ 4608 * Z ^ 3 * L ^ 2 := by
    calc
      _ ≤ 576 * (8 * Z ^ 3) * L ^ 2 := by gcongr
      _ = _ := by ring
  have hreciprocalTerm : 864 * n * Llog ≤ 1728 * Z * L := by
    calc
      _ ≤ 864 * (2 * Z) * L := by gcongr
      _ = _ := by ring
  unfold fullCellElementarySieveVariableAggregateEnvelope
  unfold fullCellElementarySievePowerAggregateEnvelope
  dsimp only
  change cellCount *
      ((4608 / Real.log 2) * area * Real.log n / n +
        576 * n ^ 3 * Llog ^ 2) +
      (864 * n * Llog) * reciprocalSum ≤ _
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hareaTerm hcubicTerm) hcellCount)
    (mul_le_mul_of_nonneg_right hreciprocalTerm hreciprocal)

theorem main3LargeAnalytic_fullCellElementaryVariableAggregate_le_powerAggregate
    (theta : ℝ) (Y Ndegree : ℕ)
    (cellCount area reciprocalSum : ℝ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hN : 4 ≤ main3LargeAnalyticSieveN theta Y)
    (hcellCount : 0 ≤ cellCount) (harea : 0 ≤ area)
    (hreciprocal : 0 ≤ reciprocalSum) :
    let Z := (Y : ℝ) ^ (1 / (32 * theta ^ 2))
    let L := 7 * (1 + Real.log (2 * (Y : ℝ)))
    fullCellElementarySieveVariableAggregateEnvelope
        (main3LargeAnalyticSieveN theta Y) Ndegree
        cellCount area reciprocalSum ≤
      fullCellElementarySievePowerAggregateEnvelope
        Z L Ndegree cellCount area reciprocalSum := by
  dsimp only
  -- Reuse the already-checked scale and logarithm definitions, with the
  -- elementary cubic loss in place of the degree-dependent conclusion.
  let y : ℝ := Y
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Z : ℝ := y ^ s
  let L : ℝ := 7 * (1 + Real.log (2 * y))
  let P : ℕ := main3LargeAnalyticSieveN theta Y
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hZpos : 0 < Z := by dsimp [Z, y]; positivity
  have hZP : Z ≤ (P : ℝ) := by
    simpa only [Z, y, s, P] using main3LargeAnalyticSieveRealScale_le theta Y
  have hPZ : (P : ℝ) ≤ 2 * Z := by
    simpa only [P, Z, y, s, main3LargeAnalyticSieveN] using
      powerRootCeilEndpoint_le_two_rpow (show 1 ≤ Y by omega) hs0
  have hL0 : 0 ≤ L := by
    dsimp [L, y]
    have hone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    have hlog : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg hone
    linarith
  -- Extract the two logarithmic comparisons by unfolding the accepted proof's
  -- input theorem would be brittle, so reproduce only their elementary bounds.
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by dsimp [y]; exact_mod_cast (show 1 ≤ Y by omega)
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hyone
  have hlogTwo0 : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogTwo1 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9.le]
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_one (by positivity : 0 < 32 * theta ^ 2)).2
    nlinarith [sq_nonneg (theta - 3)]
  have hlogZ : Real.log Z = s * Real.log y := by
    dsimp [Z]
    exact Real.log_rpow hypos s
  have hlogP : Real.log (P : ℝ) ≤ L := by
    have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
    have hmono := Real.log_le_log hPpos hPZ
    have hslog : s * Real.log y ≤ Real.log y :=
      mul_le_of_le_one_left hlogy hs1
    dsimp only [L]
    calc
      Real.log (P : ℝ) ≤ Real.log (2 * Z) := hmono
      _ = Real.log 2 + Real.log Z := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
      _ = Real.log 2 + s * Real.log y := by rw [hlogZ]
      _ ≤ 1 + Real.log (2 * y) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
        linarith [Real.log_two_lt_d9.le]
      _ ≤ 7 * (1 + Real.log (2 * y)) := by
        have hbase : 0 ≤ 1 + Real.log (2 * y) := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
          linarith
        nlinarith
  have hlargeLog : 1 + Real.log (16 * (P : ℝ) ^ 2) ≤ L := by
    have hPSq : (P : ℝ) ^ 2 ≤ 4 * Z ^ 2 := by
      nlinarith [sq_nonneg (2 * Z - (P : ℝ))]
    have harg : 16 * (P : ℝ) ^ 2 ≤ 64 * Z ^ 2 := by nlinarith
    have hmono := Real.log_le_log (by positivity : 0 < 16 * (P : ℝ) ^ 2) harg
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have hright : Real.log (64 * Z ^ 2) =
        6 * Real.log 2 + 2 * (s * Real.log y) := by
      rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0)
        (pow_ne_zero 2 hZpos.ne'), hlog64, Real.log_pow, hlogZ]
      norm_num
    have hslog : s * Real.log y ≤ Real.log y :=
      mul_le_of_le_one_left hlogy hs1
    dsimp only [L]
    calc
      1 + Real.log (16 * (P : ℝ) ^ 2) ≤
          1 + Real.log (64 * Z ^ 2) := by linarith
      _ = 1 + 6 * Real.log 2 + 2 * (s * Real.log y) := by
        rw [hright]
        ring
      _ ≤ 7 * (1 + Real.log 2 + Real.log y) := by nlinarith
      _ = 7 * (1 + Real.log (2 * y)) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
        ring
  simpa only [P, Z, L, y, s] using
    fullCellElementarySieveVariableAggregateEnvelope_le_powerAggregate
      P Ndegree Z L cellCount area reciprocalSum hN hZpos hZP hPZ hL0
        hlogP hlargeLog hcellCount harea hreciprocal

/-- The one additional power comparison needed by the elementary envelope. -/
theorem main3LargeAnalytic_outer_mesh_sieve_cube_le_workspace
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    let y : ℝ := Y
    let s : ℝ := 1 / (32 * theta ^ 2)
    let Z : ℝ := y ^ s
    let M : ℝ := main3UnbalancedM theta Y
    let Q : ℝ := y ^ (1 - s)
    M * Z ^ 3 ≤ 2 * Q := by
  dsimp only
  let y : ℝ := Y
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Z : ℝ := y ^ s
  let M : ℝ := main3UnbalancedM theta Y
  let Q : ℝ := y ^ (1 - s)
  have hypos : 0 < y := by dsimp [y]; positivity
  have hMraw : M ≤ 2 * y ^ (1 - 4 * s) := by
    have h := main3UnbalancedM_cast_le_two_mul_rpow_outerPowerLedger
      theta Y htheta hY
    have hexponent : 1 - 1 / (8 * theta ^ 2) = 1 - 4 * s := by
      dsimp [s]
      ring
    simpa only [M, y, hexponent] using h
  have hZcube : Z ^ 3 = y ^ (3 * s) := by
    dsimp only [Z]
    rw [← Real.rpow_mul_natCast hypos.le]
    congr 1
    norm_num
    ring
  calc
    M * Z ^ 3 ≤ (2 * y ^ (1 - 4 * s)) * Z ^ 3 := by gcongr
    _ = 2 * y ^ (1 - s) := by
      rw [hZcube]
      rw [show 2 * y ^ (1 - 4 * s) * y ^ (3 * s) =
        2 * (y ^ (1 - 4 * s) * y ^ (3 * s)) by ring,
        ← Real.rpow_add hypos]
      congr 2
      ring
    _ = 2 * Q := by rfl

theorem fullCellElementarySievePowerAggregateEnvelope_le_coarseKeyEnvelope
    (theta S T cellCount area Z L reciprocalSum : ℝ) (D : ℕ)
    (htheta : 1 ≤ theta) (hS : 1 ≤ S) (hT : 0 ≤ T)
    (_hcellCount : 0 ≤ cellCount) (_harea : 0 ≤ area)
    (hZ : 0 < Z) (hL0 : 0 ≤ L) (hreciprocal : 0 ≤ reciprocalSum)
    (hL : L ≤ 7 * S)
    (_hdegree : (D : ℝ) + 1 ≤ 2 * theta ^ 3)
    (hcellArea : cellCount * area / Z ≤ 31363200 * S * T)
    (hcellZ : cellCount * Z ^ 3 ≤ 7200 * S * T)
    (hZreciprocal : Z * reciprocalSum ≤
      3000000000000000 * S ^ 3 * T)
    (_hreciprocalUpper : reciprocalSum ≤
      3000000000000000 * S ^ 3 * T) :
    2 * fullCellElementarySievePowerAggregateEnvelope
          Z L D cellCount area reciprocalSum ≤
      main3LargeAnalyticCoarseKeyEnvelopeConstant *
        theta ^ 6 * S ^ 4 * T := by
  have hthetaSixOne : 1 ≤ theta ^ 6 := one_le_pow₀ htheta
  have hSSq : S ^ 2 ≤ S ^ 4 := pow_le_pow_right₀ hS (by omega)
  have hSCube : S ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS (by omega)
  have hthetaLift : S ^ 4 ≤ theta ^ 6 * S ^ 4 := by
    have hnonneg : 0 ≤ S ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hthetaSixOne hnonneg]
  have hLsq : L ^ 2 ≤ 49 * S ^ 2 := by
    calc
      L ^ 2 ≤ (7 * S) ^ 2 := pow_le_pow_left₀ hL0 hL 2
      _ = 49 * S ^ 2 := by ring
  have hS2T : S ^ 2 * T ≤ theta ^ 6 * S ^ 4 * T := by
    calc
      S ^ 2 * T ≤ S ^ 4 * T := by gcongr
      _ ≤ theta ^ 6 * S ^ 4 * T :=
        mul_le_mul_of_nonneg_right hthetaLift hT
  have hS3T : S ^ 3 * T ≤ theta ^ 6 * S ^ 4 * T := by
    calc
      S ^ 3 * T ≤ S ^ 4 * T := by gcongr
      _ ≤ theta ^ 6 * S ^ 4 * T :=
        mul_le_mul_of_nonneg_right hthetaLift hT
  have hS4T : S ^ 4 * T ≤ theta ^ 6 * S ^ 4 * T :=
    mul_le_mul_of_nonneg_right hthetaLift hT
  have hareaTerm :
      cellCount * (9216 * area * L / Z) ≤
        2023302758400 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      _ = 9216 * (cellCount * area / Z) * L := by ring
      _ ≤ 9216 * (31363200 * S * T) * (7 * S) := by gcongr
      _ = 2023302758400 * (S ^ 2 * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS2T (by norm_num)
  have hcubicTerm :
      cellCount * (4608 * Z ^ 3 * L ^ 2) ≤
        1625702400 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      _ = 4608 * (cellCount * Z ^ 3) * L ^ 2 := by ring
      _ ≤ 4608 * (7200 * S * T) * (49 * S ^ 2) := by gcongr
      _ = 1625702400 * (S ^ 3 * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS3T (by norm_num)
  have hreciprocalTerm :
      (1728 * Z * L) * reciprocalSum ≤
        36288000000000000000 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      _ = 1728 * L * (Z * reciprocalSum) := by ring
      _ ≤ 1728 * (7 * S) *
          (3000000000000000 * S ^ 3 * T) := by gcongr
      _ = 36288000000000000000 * (S ^ 4 * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS4T (by norm_num)
  unfold fullCellElementarySievePowerAggregateEnvelope
  unfold main3LargeAnalyticCoarseKeyEnvelopeConstant
  have htarget : 0 ≤ theta ^ 6 * S ^ 4 * T := by positivity
  nlinarith

end

end PellPaper

#print axioms PellPaper.sum_fullCellElementarySieveEnvelope_le_variableAggregate
#print axioms PellPaper.main3LargeAnalytic_outer_mesh_sieve_cube_le_workspace
#print axioms PellPaper.fullCellElementarySievePowerAggregateEnvelope_le_coarseKeyEnvelope
