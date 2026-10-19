import Pell.Main3LargeAnalyticVariableCellEnvelopeSum
import Pell.Main3LargeAnalyticUniformSieveScale
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Coarse power-form bound for the variable-cell sieve envelope

This workspace replaces the rounded sieve parameter by a positive real scale
`Z`, retaining the reciprocal `1 / Z` saving and the `Z^2` loss.  The caller
supplies the two elementary logarithmic comparisons; Main3 will take
`Z = Y^(1/(32*theta^2))`.
-/

namespace PellPaper

noncomputable section

/-- A monotone coarse form of the variable-cell aggregate envelope. -/
def fullCellOddDegreeSievePowerAggregateEnvelope
    (Z L : ℝ) (D : ℕ) (cellCount area reciprocalSum : ℝ) : ℝ :=
  cellCount *
      (9216 * area * L / Z +
        256 * ((D : ℝ) + 1) ^ 2 * Z ^ 2 * L ^ 2) +
    (1536 * Z * L + 96 * ((D : ℝ) + 1) ^ 2 * L) * reciprocalSum

/-- If `Z <= N <= 2Z`, then the exact variable-cell aggregate is bounded by
the power-form envelope above. -/
theorem fullCellOddDegreeSieveVariableAggregateEnvelope_le_powerAggregate
    (N D : ℕ) (Z L cellCount area reciprocalSum : ℝ)
    (hN : 4 ≤ N) (hZ : 0 < Z)
    (hZN : Z ≤ (N : ℝ)) (hNZ : (N : ℝ) ≤ 2 * Z)
    (hL : 0 ≤ L)
    (hlogN : Real.log (N : ℝ) ≤ L)
    (hlargeLog : 1 + Real.log (16 * (N : ℝ) ^ 2) ≤ L)
    (hcellCount : 0 ≤ cellCount) (harea : 0 ≤ area)
    (hreciprocal : 0 ≤ reciprocalSum) :
    fullCellOddDegreeSieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum ≤
      fullCellOddDegreeSievePowerAggregateEnvelope
        Z L D cellCount area reciprocalSum := by
  let n : ℝ := N
  let degree : ℝ := (D : ℝ) + 1
  let Llog : ℝ := 1 + Real.log (16 * n ^ 2)
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hn0 : 0 ≤ n := hn.le
  have hlogN0 : 0 ≤ Real.log n := by
    exact Real.log_nonneg (by
      dsimp [n]
      exact_mod_cast (show 1 ≤ N by omega))
  have hLlog0 : 0 ≤ Llog := by
    dsimp [Llog, n]
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9 |>.le
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoefficient : 4608 / Real.log 2 ≤ (9216 : ℝ) := by
    apply (div_le_iff₀ hlogTwoPos).2
    nlinarith
  have hinv : 1 / n ≤ 1 / Z := by
    exact one_div_le_one_div_of_le hZ (by simpa only [n] using hZN)
  have hareaTerm :
      (4608 / Real.log 2) * area * Real.log n / n ≤
        9216 * area * L / Z := by
    calc
      (4608 / Real.log 2) * area * Real.log n / n =
          ((4608 / Real.log 2) * area * Real.log n) * (1 / n) := by ring
      _ ≤ (9216 * area * L) * (1 / Z) := by
        gcongr
      _ = 9216 * area * L / Z := by ring
  have hnSq : n ^ 2 ≤ 4 * Z ^ 2 := by
    nlinarith [sq_nonneg (2 * Z - n)]
  have hLlogSq : Llog ^ 2 ≤ L ^ 2 := by
    exact (sq_le_sq₀ hLlog0 hL).2
      (by simpa only [Llog, n] using hlargeLog)
  have hdegreeTerm :
      64 * degree ^ 2 * n ^ 2 * Llog ^ 2 ≤
        256 * degree ^ 2 * Z ^ 2 * L ^ 2 := by
    calc
      64 * degree ^ 2 * n ^ 2 * Llog ^ 2 ≤
          64 * degree ^ 2 * (4 * Z ^ 2) * L ^ 2 := by
        gcongr
      _ = 256 * degree ^ 2 * Z ^ 2 * L ^ 2 := by ring
  have hlinearReciprocal :
      768 * n * Llog ≤ 1536 * Z * L := by
    calc
      768 * n * Llog ≤ 768 * (2 * Z) * L := by
        gcongr
      _ = 1536 * Z * L := by ring
  have hquadraticReciprocal :
      96 * degree ^ 2 * Llog ≤ 96 * degree ^ 2 * L := by
    gcongr
  unfold fullCellOddDegreeSieveVariableAggregateEnvelope
  unfold fullCellOddDegreeSievePowerAggregateEnvelope
  dsimp only
  change cellCount *
      ((4608 / Real.log 2) * area * Real.log n / n +
        64 * degree ^ 2 * n ^ 2 * Llog ^ 2) +
      (768 * n * Llog + 96 * degree ^ 2 * Llog) * reciprocalSum ≤ _
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add hareaTerm hdegreeTerm) hcellCount)
    (mul_le_mul_of_nonneg_right
      (add_le_add hlinearReciprocal hquadraticReciprocal) hreciprocal)

/-- Main3 specialization with `Z = Y^(1/(32*theta^2))` and one standard
dyadic logarithm. -/
theorem main3LargeAnalytic_fullCellVariableAggregate_le_powerAggregate
    (theta : ℝ) (Y Ndegree : ℕ)
    (cellCount area reciprocalSum : ℝ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hN : 4 ≤ main3LargeAnalyticSieveN theta Y)
    (hcellCount : 0 ≤ cellCount) (harea : 0 ≤ area)
    (hreciprocal : 0 ≤ reciprocalSum) :
    let Z := (Y : ℝ) ^ (1 / (32 * theta ^ 2))
    let L := 7 * (1 + Real.log (2 * (Y : ℝ)))
    fullCellOddDegreeSieveVariableAggregateEnvelope
        (main3LargeAnalyticSieveN theta Y) Ndegree
        cellCount area reciprocalSum ≤
      fullCellOddDegreeSievePowerAggregateEnvelope
        Z L Ndegree cellCount area reciprocalSum := by
  dsimp only
  let y : ℝ := Y
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Z : ℝ := y ^ s
  let L₀ : ℝ := 1 + Real.log (2 * y)
  let L : ℝ := 7 * L₀
  let P : ℕ := main3LargeAnalyticSieveN theta Y
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hyone
  have hthetaSqPos : 0 < theta ^ 2 := by positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_one (by positivity : 0 < 32 * theta ^ 2)).2
    nlinarith [sq_nonneg (theta - 3)]
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact Real.rpow_pos_of_pos hypos _
  have hZone : 1 ≤ Z := by
    calc
      (1 : ℝ) = y ^ (0 : ℝ) := by simp
      _ ≤ y ^ s := Real.rpow_le_rpow_of_exponent_le hyone hs0
      _ = Z := rfl
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hZP : Z ≤ (P : ℝ) := by
    simpa only [Z, y, s, P] using
      main3LargeAnalyticSieveRealScale_le theta Y
  have hPZ : (P : ℝ) ≤ 2 * Z := by
    simpa only [P, Z, y, s, main3LargeAnalyticSieveN] using
      powerRootCeilEndpoint_le_two_rpow (show 1 ≤ Y by omega) hs0
  have hlogZ : Real.log Z = s * Real.log y := by
    dsimp [Z]
    exact Real.log_rpow hypos s
  have hlogTwo0 : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogTwo1 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9.le]
  have hL₀ : 0 ≤ L₀ := by
    dsimp [L₀]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
    linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlogP : Real.log (P : ℝ) ≤ L := by
    have hmono : Real.log (P : ℝ) ≤ Real.log (2 * Z) :=
      Real.log_le_log hPpos hPZ
    have hslog : s * Real.log y ≤ Real.log y := by
      exact mul_le_of_le_one_left hlogy hs1
    calc
      Real.log (P : ℝ) ≤ Real.log (2 * Z) := hmono
      _ = Real.log 2 + Real.log Z := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
      _ = Real.log 2 + s * Real.log y := by rw [hlogZ]
      _ ≤ L₀ := by
        dsimp [L₀]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
        linarith
      _ ≤ L := by dsimp [L]; nlinarith
  have hlargeLog : 1 + Real.log (16 * (P : ℝ) ^ 2) ≤ L := by
    have hPSq : (P : ℝ) ^ 2 ≤ 4 * Z ^ 2 := by
      nlinarith [sq_nonneg (2 * Z - (P : ℝ))]
    have harg : 16 * (P : ℝ) ^ 2 ≤ 64 * Z ^ 2 := by nlinarith
    have hargPos : 0 < 16 * (P : ℝ) ^ 2 := by positivity
    have hmono : Real.log (16 * (P : ℝ) ^ 2) ≤
        Real.log (64 * Z ^ 2) := Real.log_le_log hargPos harg
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have hlogRight : Real.log (64 * Z ^ 2) =
        6 * Real.log 2 + 2 * (s * Real.log y) := by
      rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0)
        (pow_ne_zero 2 hZpos.ne'), hlog64, Real.log_pow, hlogZ]
      norm_num
    have hslog : s * Real.log y ≤ Real.log y := by
      exact mul_le_of_le_one_left hlogy hs1
    calc
      1 + Real.log (16 * (P : ℝ) ^ 2) ≤
          1 + Real.log (64 * Z ^ 2) := by linarith
      _ = 1 + 6 * Real.log 2 + 2 * (s * Real.log y) := by
        rw [hlogRight]
        ring
      _ ≤ 7 * (1 + Real.log 2 + Real.log y) := by nlinarith
      _ = L := by
        dsimp [L, L₀]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hypos.ne']
        ring
  simpa only [P, Z, L, y, s] using
    fullCellOddDegreeSieveVariableAggregateEnvelope_le_powerAggregate
      P Ndegree Z L cellCount area reciprocalSum hN hZpos hZP hPZ hL
        hlogP hlargeLog hcellCount harea hreciprocal

end

end PellPaper
