import Pell.FullCellActualLogMajorants
import Pell.Main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
import Pell.Main3LargeAnalyticTargetFibreCoordinateLogBounds
import Pell.Main3LargeAnalyticTargetFibreRadiusLowerBounds
import Pell.ShiftedSquareAuxiliarySurfaceLevelWeight
import Mathlib.Tactic

/-!
# Logarithmic sieve budgets for the intrinsic main3 eliminant

This frozen candidate expands the coefficient-height ledger of the literal
fixed-key, fixed-cell eliminant.  The target-basis entry height `L` and the
two rectangle scales `U,V` remain explicit.  One maximum threshold then
supplies exactly the two logarithmic hypotheses of the generic intrinsic
odd-degree square sieve.

No character-sum or Weil estimate is asserted here.
-/

namespace PellPaper

noncomputable section

/-- Uniform logarithmic majorant for the fixed-cell factor height.  The
cofactor rank is replaced by its proved strict upper bound `2*(B+1)`, while
the constants `6` and `2` are the literal source and target coordinate-log
budgets. -/
def main3LargeAnalyticFixedKeyFactorLogMajorant
    (theta : ℝ) (Y B : ℕ) : ℝ :=
  (B : ℝ) * Real.log 2 + Real.log ((B : ℝ) + 1) +
    ((2 * (B + 1) : ℕ) : ℝ) *
      (Real.log ((2 * (B + 1) : ℕ) : ℝ) / 2 +
        (6 + 2 * (B : ℝ)) * theta * Real.log (Y : ℝ))

/-- Uniform logarithmic majorant for `log (Hraw+1)`.  The three copies of
`log 2` are respectively the outer `+1` loss and the two factor-height
ceiling losses.  The final `6*log Y` is the sum of the surface-level and
surface-coefficient budgets. -/
def main3LargeAnalyticIntrinsicEliminantRawLogMajorant
    (theta : ℝ) (Y B : ℕ) : ℝ :=
  3 * Real.log 2 + Real.log 6 + Real.log ((B : ℝ) + 1) +
    2 * main3LargeAnalyticFixedKeyFactorLogMajorant theta Y B +
      6 * Real.log (Y : ℝ)

private theorem main3LargeAnalytic_fixedKeyCell_coordinateBound_log_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty) :
    (1 : ℝ) ≤ (main3LargeAnalyticFixedKeySourceCoordinateBound
        (shiftedSquareA h v) D key : ℝ) ∧
      Real.log (main3LargeAnalyticFixedKeySourceCoordinateBound
          (shiftedSquareA h v) D key : ℝ) ≤
        6 * theta * Real.log (Y : ℝ) ∧
      (1 : ℝ) ≤ (main3LargeAnalyticFixedKeyTargetCoordinateBound
          (shiftedSquareA h v) Y key : ℝ) ∧
      Real.log (main3LargeAnalyticFixedKeyTargetCoordinateBound
          (shiftedSquareA h v) Y key : ℝ) ≤
        2 * theta * Real.log (Y : ℝ) := by
  obtain ⟨z, hz⟩ := hnonempty
  let q := main3GeneralBidegreePointVectorEquiv z
  let y : Fin 2 → ℤ := q.2
  have hqImage : q ∈
      main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell := by
    rw [main3LargeAnalyticFixedKeyCellVectorImage]
    exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
  have hqFibre : q ∈
      main3LargeAnalyticFixedKeyCellTargetFibre htheta hY hi key cell y :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y q).mpr ⟨hqImage, rfl⟩
  let p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y := ⟨q, hqFibre⟩
  have hsourceOne :=
    one_le_main3LargeAnalyticFixedKeySourceCoordinateRadius_of_targetFibrePoint
      htheta hY hi key cell y p₀
  have htargetOne :=
    one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetFibrePoint
      htheta hY hi key cell y p₀
  have hsourceLog :=
    log_main3LargeAnalyticFixedKeySourceCoordinateRadius_le
      htheta hY hi key cell y p₀
  have htargetLog :=
    log_main3LargeAnalyticFixedKeyTargetCoordinateRadius_le
      htheta hY hi key cell y p₀
  let S : ℤ := main3LargeAnalyticFixedKeySourceCoordinateBound
    (shiftedSquareA h v) D key
  let T : ℤ := main3LargeAnalyticFixedKeyTargetCoordinateBound
    (shiftedSquareA h v) Y key
  have hSoneZ : (1 : ℤ) ≤ S := by
    dsimp [S, main3LargeAnalyticFixedKeySourceCoordinateBound]
    exact Int.le_floor.mpr (by simpa only [Int.cast_one] using hsourceOne)
  have hToneZ : (1 : ℤ) ≤ T := by
    dsimp [T, main3LargeAnalyticFixedKeyTargetCoordinateBound]
    exact Int.le_floor.mpr (by simpa only [Int.cast_one] using htargetOne)
  have hSone : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hSoneZ
  have hTone : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hToneZ
  have hSle : (S : ℝ) ≤
      main3LargeAnalyticFixedKeySourceCoordinateRadius
        (shiftedSquareA h v) D key := by
    dsimp [S, main3LargeAnalyticFixedKeySourceCoordinateBound]
    exact Int.floor_le _
  have hTle : (T : ℝ) ≤
      main3LargeAnalyticFixedKeyTargetCoordinateRadius
        (shiftedSquareA h v) Y key := by
    dsimp [T, main3LargeAnalyticFixedKeyTargetCoordinateBound]
    exact Int.floor_le _
  have hSlog : Real.log (S : ℝ) ≤
      6 * theta * Real.log (Y : ℝ) :=
    (Real.log_le_log (by positivity) hSle).trans hsourceLog
  have hTlog : Real.log (T : ℝ) ≤
      2 * theta * Real.log (Y : ℝ) :=
    (Real.log_le_log (by positivity) hTle).trans htargetLog
  simpa only [S, T] using ⟨hSone, hSlog, hTone, hTlog⟩

/-- A nonempty exact cell makes the fixed factor height at least one.  This is
the precise input needed to charge the positive-natural ceiling by one factor
of two. -/
theorem one_le_main3LargeAnalyticFixedKeyFactorHeight_of_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    1 ≤ main3LargeAnalyticFixedKeyFactorHeight B data.rank
      (shiftedSquareA h v) D Y key := by
  have hcoords := main3LargeAnalytic_fixedKeyCell_coordinateBound_log_package
    htheta hY hi key cell hnonempty
  let S : ℤ := main3LargeAnalyticFixedKeySourceCoordinateBound
    (shiftedSquareA h v) D key
  let T : ℤ := main3LargeAnalyticFixedKeyTargetCoordinateBound
    (shiftedSquareA h v) Y key
  have hSone : (1 : ℝ) ≤ (S : ℝ) := by
    simpa only [S] using hcoords.1
  have hTone : (1 : ℝ) ≤ (T : ℝ) := by
    simpa only [T] using hcoords.2.2.1
  have hSTone : (1 : ℝ) ≤ (((S * T ^ B : ℤ) : ℝ)) := by
    push_cast
    have hTpow : (1 : ℝ) ≤ (T : ℝ) ^ B := one_le_pow₀ hTone
    simpa only [one_mul] using
      mul_le_mul hSone hTpow (by norm_num) (by positivity)
  have hauxone : 1 ≤ main3LargeAnalyticFixedKeyAuxiliaryHeight B data.rank
      (shiftedSquareA h v) D Y key := by
    rw [main3LargeAnalyticFixedKeyAuxiliaryHeight]
    change 1 ≤ (Real.sqrt (data.rank : ℝ) * (((S * T ^ B : ℤ) : ℝ))) ^ data.rank
    by_cases hrank : data.rank = 0
    · simp [hrank]
    · have hrankOneNat : 1 ≤ data.rank := Nat.one_le_iff_ne_zero.mpr hrank
      have hrankOne : (1 : ℝ) ≤ data.rank := by exact_mod_cast hrankOneNat
      have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (data.rank : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hrankOne
      have hbase : (1 : ℝ) ≤
          Real.sqrt (data.rank : ℝ) * (((S * T ^ B : ℤ) : ℝ)) := by
        simpa only [one_mul] using
          mul_le_mul hsqrtOne hSTone (by norm_num) (Real.sqrt_nonneg _)
      exact one_le_pow₀ hbase
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  have hBone : (1 : ℝ) ≤ (B : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le B)
  rw [main3LargeAnalyticFixedKeyFactorHeight]
  calc
    (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ (2 : ℝ) ^ B * ((B : ℝ) + 1) *
        main3LargeAnalyticFixedKeyAuxiliaryHeight B data.rank
          (shiftedSquareA h v) D Y key :=
      mul_le_mul (mul_le_mul htwo hBone (by norm_num) (by positivity))
        hauxone (by norm_num) (by positivity)

/-- The logarithm of the actual fixed-cell factor height is bounded by the
uniform full-column ledger. -/
theorem log_main3LargeAnalyticFixedKeyFactorHeight_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    Real.log (main3LargeAnalyticFixedKeyFactorHeight B data.rank
      (shiftedSquareA h v) D Y key) ≤
        main3LargeAnalyticFixedKeyFactorLogMajorant theta Y B := by
  have hcoords := main3LargeAnalytic_fixedKeyCell_coordinateBound_log_package
    htheta hY hi key cell hnonempty
  let S : ℤ := main3LargeAnalyticFixedKeySourceCoordinateBound
    (shiftedSquareA h v) D key
  let T : ℤ := main3LargeAnalyticFixedKeyTargetCoordinateBound
    (shiftedSquareA h v) Y key
  let Hcol : ℕ := 2 * (B + 1)
  let Q : ℝ :=
    Real.log (Hcol : ℝ) / 2 +
      (6 + 2 * (B : ℝ)) * theta * Real.log (Y : ℝ)
  have hSone : (1 : ℝ) ≤ (S : ℝ) := by
    simpa only [S] using hcoords.1
  have hSlog : Real.log (S : ℝ) ≤ 6 * theta * Real.log (Y : ℝ) := by
    simpa only [S] using hcoords.2.1
  have hTone : (1 : ℝ) ≤ (T : ℝ) := by
    simpa only [T] using hcoords.2.2.1
  have hTlog : Real.log (T : ℝ) ≤ 2 * theta * Real.log (Y : ℝ) := by
    simpa only [T] using hcoords.2.2.2
  have hSpos : (0 : ℝ) < S := zero_lt_one.trans_le hSone
  have hTpos : (0 : ℝ) < T := zero_lt_one.trans_le hTone
  have hSTcast : (((S * T ^ B : ℤ) : ℝ)) = (S : ℝ) * (T : ℝ) ^ B := by
    push_cast
    rfl
  have hSTpos : (0 : ℝ) < (((S * T ^ B : ℤ) : ℝ)) := by
    rw [hSTcast]
    positivity
  have hHcolPosNat : 0 < Hcol := by dsimp [Hcol]; omega
  have hHcolOne : (1 : ℝ) ≤ Hcol := by exact_mod_cast hHcolPosNat
  have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    have hlogHcol : 0 ≤ Real.log (Hcol : ℝ) := Real.log_nonneg hHcolOne
    have hthetaNonneg : 0 ≤ theta := by linarith
    positivity
  have hauxPos : 0 < main3LargeAnalyticFixedKeyAuxiliaryHeight B data.rank
      (shiftedSquareA h v) D Y key := by
    rw [main3LargeAnalyticFixedKeyAuxiliaryHeight]
    change 0 < (Real.sqrt (data.rank : ℝ) * (((S * T ^ B : ℤ) : ℝ))) ^ data.rank
    by_cases hrank : data.rank = 0
    · simp [hrank]
    · exact pow_pos
        (mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hrank)) hSTpos)
        data.rank
  have hauxLog :
      Real.log (main3LargeAnalyticFixedKeyAuxiliaryHeight B data.rank
          (shiftedSquareA h v) D Y key) ≤ (Hcol : ℝ) * Q := by
    by_cases hrank : data.rank = 0
    · rw [main3LargeAnalyticFixedKeyAuxiliaryHeight]
      simp only [hrank, Nat.cast_zero, Real.sqrt_zero, zero_mul, pow_zero,
        Real.log_one]
      exact mul_nonneg (by positivity) hQnonneg
    · have hrankPosNat : 0 < data.rank := Nat.pos_of_ne_zero hrank
      have hrankPos : (0 : ℝ) < data.rank := by exact_mod_cast hrankPosNat
      have hrankLeNat : data.rank ≤ Hcol := by
        dsimp [Hcol]
        exact Nat.le_of_lt data.rank_lt
      have hrankLe : (data.rank : ℝ) ≤ Hcol := by exact_mod_cast hrankLeNat
      have hlogRank : Real.log (data.rank : ℝ) ≤ Real.log (Hcol : ℝ) :=
        Real.log_le_log hrankPos hrankLe
      have hlogSqrt : Real.log (Real.sqrt (data.rank : ℝ)) ≤
          Real.log (Hcol : ℝ) / 2 := by
        rw [Real.log_sqrt (by positivity)]
        linarith
      have hBTlog : (B : ℝ) * Real.log (T : ℝ) ≤
          (B : ℝ) * (2 * theta * Real.log (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hTlog (by positivity)
      have hcoordinateLog :
          Real.log (S : ℝ) + (B : ℝ) * Real.log (T : ℝ) ≤
            (6 + 2 * (B : ℝ)) * theta * Real.log (Y : ℝ) := by
        calc
          Real.log (S : ℝ) + (B : ℝ) * Real.log (T : ℝ) ≤
              6 * theta * Real.log (Y : ℝ) +
                (B : ℝ) * (2 * theta * Real.log (Y : ℝ)) :=
            add_le_add hSlog hBTlog
          _ = (6 + 2 * (B : ℝ)) * theta * Real.log (Y : ℝ) := by ring
      have hinner :
          Real.log (Real.sqrt (data.rank : ℝ)) + Real.log (S : ℝ) +
              (B : ℝ) * Real.log (T : ℝ) ≤ Q := by
        dsimp [Q]
        linarith
      have hauxEq :
          Real.log (main3LargeAnalyticFixedKeyAuxiliaryHeight B data.rank
              (shiftedSquareA h v) D Y key) =
            (data.rank : ℝ) *
              (Real.log (Real.sqrt (data.rank : ℝ)) + Real.log (S : ℝ) +
                (B : ℝ) * Real.log (T : ℝ)) := by
        rw [main3LargeAnalyticFixedKeyAuxiliaryHeight]
        change Real.log
            ((Real.sqrt (data.rank : ℝ) * (((S * T ^ B : ℤ) : ℝ))) ^
              data.rank) = _
        rw [Real.log_pow,
          Real.log_mul (Real.sqrt_pos.2 hrankPos).ne' hSTpos.ne', hSTcast,
          Real.log_mul hSpos.ne' (pow_ne_zero _ hTpos.ne'), Real.log_pow]
        ring
      rw [hauxEq]
      calc
        (data.rank : ℝ) *
            (Real.log (Real.sqrt (data.rank : ℝ)) + Real.log (S : ℝ) +
              (B : ℝ) * Real.log (T : ℝ)) ≤
            (data.rank : ℝ) * Q :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ (Hcol : ℝ) * Q :=
          mul_le_mul_of_nonneg_right hrankLe hQnonneg
  have hfactorEq :
      Real.log (main3LargeAnalyticFixedKeyFactorHeight B data.rank
          (shiftedSquareA h v) D Y key) =
        (B : ℝ) * Real.log 2 + Real.log ((B : ℝ) + 1) +
          Real.log (main3LargeAnalyticFixedKeyAuxiliaryHeight B data.rank
            (shiftedSquareA h v) D Y key) := by
    rw [main3LargeAnalyticFixedKeyFactorHeight,
      Real.log_mul
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) hauxPos.ne',
      Real.log_mul (pow_ne_zero _ (by norm_num)) (by positivity), Real.log_pow]
  rw [hfactorEq, main3LargeAnalyticFixedKeyFactorLogMajorant]
  dsimp [Hcol, Q] at hauxLog
  linarith

/-- Membership in the literal auxiliary-key gate bounds the logarithm of the
nonzero affine surface level by `3*log Y`.  Before logarithmic absorption the
proof gives the explicit pointwise bound `|level| ≤ 2178*|shift|`. -/
theorem log_shiftedSquareAuxiliaryKeySurfaceLevel_natAbs_le_three_mul_log
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    Real.log ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤
      3 * Real.log (Y : ℝ) := by
  let a : ℤ := shiftedSquareA h v
  let R : ℕ := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  have hkey' : key ∈ shiftedSquareAuxiliaryKeys R := by
    simpa only [R, main3LargeAnalytic_blockAuxiliaryKeyGate] using hkey
  have hlevel := shiftedSquareAuxiliaryKeySurfaceLevel_pos_and_natAbs_le hkey'
  have ha : a ≠ 0 := by
    dsimp [a]
    exact main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have habsOne : (1 : ℝ) ≤ |(a : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt |(a : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt habsOne
  have hRlt : (R : ℝ) < 32 * Real.sqrt |(a : ℝ)| + 1 := by
    simpa only [R, a] using (main3LargeAnalytic_auxiliaryC₀Ceiling_spec h v).2
  have hRle : (R : ℝ) ≤ 33 * Real.sqrt |(a : ℝ)| := by
    linarith
  have hRsq : (R : ℝ) ^ 2 ≤ 1089 * |(a : ℝ)| := by
    calc
      (R : ℝ) ^ 2 ≤ (33 * Real.sqrt |(a : ℝ)|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hRle 2
      _ = 1089 * |(a : ℝ)| := by
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
        norm_num
  have hlevelCast :
      ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤
        2 * (R : ℝ) ^ 2 := by
    exact_mod_cast hlevel.2
  have hlevelShift :
      ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤
        2178 * |(a : ℝ)| := by
    calc
      ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤
          2 * (R : ℝ) ^ 2 := hlevelCast
      _ ≤ 2 * (1089 * |(a : ℝ)|) := mul_le_mul_of_nonneg_left hRsq (by norm_num)
      _ = 2178 * |(a : ℝ)| := by ring
  have hlevelPos :
      (0 : ℝ) < (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hlevel.1.ne'
  have habsPos : (0 : ℝ) < |(a : ℝ)| := zero_lt_one.trans_le habsOne
  have hlogLevel :
      Real.log ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤
        Real.log 2178 + Real.log |(a : ℝ)| := by
    calc
      Real.log ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤
          Real.log (2178 * |(a : ℝ)|) :=
        Real.log_le_log hlevelPos hlevelShift
      _ = Real.log 2178 + Real.log |(a : ℝ)| := by
        rw [Real.log_mul (by norm_num : (2178 : ℝ) ≠ 0) habsPos.ne']
  have hlog2178 : Real.log 2178 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2178 ≤ Y by omega))
  have hloga : Real.log |(a : ℝ)| ≤ 2 * Real.log (Y : ℝ) := by
    simpa only [a] using
      main3LargeAnalytic_log_abs_shift_le_two_mul_log htheta hY hi
  linarith

/-- The fixed surface-coefficient height `8*|shift|+4` has logarithmic size
at most `3*log Y`. -/
theorem log_main3LargeAnalyticIntrinsicSurfaceCoefficientHeight_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Real.log ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℝ) ≤
      3 * Real.log (Y : ℝ) := by
  let a : ℤ := shiftedSquareA h v
  have ha : a ≠ 0 := by
    dsimp [a]
    exact main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have habsPosNat : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hheightNat : 8 * a.natAbs + 4 ≤ 12 * a.natAbs := by omega
  have hheight : ((8 * a.natAbs + 4 : ℕ) : ℝ) ≤ 12 * |(a : ℝ)| := by
    rw [show (12 : ℝ) * |(a : ℝ)| = ((12 * a.natAbs : ℕ) : ℝ) by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hheightNat
  have hleftPos : (0 : ℝ) < ((8 * a.natAbs + 4 : ℕ) : ℝ) := by positivity
  have habsPos : (0 : ℝ) < |(a : ℝ)| := by
    exact abs_pos.mpr (by exact_mod_cast ha)
  have hlogHeight :
      Real.log ((8 * a.natAbs + 4 : ℕ) : ℝ) ≤
        Real.log 12 + Real.log |(a : ℝ)| := by
    calc
      Real.log ((8 * a.natAbs + 4 : ℕ) : ℝ) ≤
          Real.log (12 * |(a : ℝ)|) :=
        Real.log_le_log hleftPos hheight
      _ = Real.log 12 + Real.log |(a : ℝ)| := by
        rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) habsPos.ne']
  have hlog12 : Real.log 12 ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 12 ≤ Y by omega))
  have hloga : Real.log |(a : ℝ)| ≤ 2 * Real.log (Y : ℝ) := by
    simpa only [a] using
      main3LargeAnalytic_log_abs_shift_le_two_mul_log htheta hY hi
  simpa only [a] using (show
    Real.log ((8 * a.natAbs + 4 : ℕ) : ℝ) ≤
      3 * Real.log (Y : ℝ) by linarith)

/-- The literal pre-substitution eliminant height, including its outer
`+1`, is controlled by the explicit raw logarithmic ledger. -/
theorem log_main3LargeAnalyticIntrinsicEliminantRawHeight_add_one_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    Real.log
        ((main3LargeAnalyticIntrinsicEliminantRawHeight
          htheta hY hi key cell data : ℝ) + 1) ≤
      main3LargeAnalyticIntrinsicEliminantRawLogMajorant theta Y B := by
  let b : ℕ := data.residualDegree
  let HFreal : ℝ := main3LargeAnalyticFixedKeyFactorHeight B data.rank
    (shiftedSquareA h v) D Y key
  let HF : ℕ := positiveNatCeil HFreal
  let c : ℕ := (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs
  let HG : ℕ := 8 * (shiftedSquareA h v).natAbs + 4
  let Hraw : ℕ := main3LargeAnalyticIntrinsicEliminantRawHeight
    htheta hY hi key cell data
  have hHFone : (1 : ℝ) ≤ HFreal := by
    dsimp [HFreal]
    exact one_le_main3LargeAnalyticFixedKeyFactorHeight_of_nonempty
      htheta hY hi key cell hnonempty data
  have hHFrealPos : 0 < HFreal := zero_lt_one.trans_le hHFone
  have hHFlog : Real.log HFreal ≤
      main3LargeAnalyticFixedKeyFactorLogMajorant theta Y B := by
    dsimp [HFreal]
    exact log_main3LargeAnalyticFixedKeyFactorHeight_le
      htheta hY hi key cell hnonempty data
  have hHFceil : (HF : ℝ) ≤ 2 * HFreal := by
    have hceil := positiveNatCeil_le_add_one (zero_le_one.trans hHFone)
    dsimp [HF]
    dsimp [HFreal] at hceil ⊢
    linarith
  have hHFposNat : 0 < HF := by
    dsimp [HF]
    exact positiveNatCeil_pos _
  have hHFpos : (0 : ℝ) < HF := by exact_mod_cast hHFposNat
  have hlogHF : Real.log (HF : ℝ) ≤
      Real.log 2 + main3LargeAnalyticFixedKeyFactorLogMajorant theta Y B := by
    calc
      Real.log (HF : ℝ) ≤ Real.log (2 * HFreal) :=
        Real.log_le_log hHFpos hHFceil
      _ = Real.log 2 + Real.log HFreal := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHFrealPos.ne']
      _ ≤ Real.log 2 +
          main3LargeAnalyticFixedKeyFactorLogMajorant theta Y B := by
        linarith
  have hcPosNat : 0 < c := by
    dsimp [c]
    exact Int.natAbs_pos.mpr data.surfaceLevel_ne_zero
  have hcPos : (0 : ℝ) < c := by exact_mod_cast hcPosNat
  have hHGPosNat : 0 < HG := by dsimp [HG]; omega
  have hHGPos : (0 : ℝ) < HG := by exact_mod_cast hHGPosNat
  have hlevelLog : Real.log (c : ℝ) ≤ 3 * Real.log (Y : ℝ) := by
    dsimp [c]
    exact log_shiftedSquareAuxiliaryKeySurfaceLevel_natAbs_le_three_mul_log
      htheta hY hi key hkey
  have hsurfaceLog : Real.log (HG : ℝ) ≤ 3 * Real.log (Y : ℝ) := by
    dsimp [HG]
    exact log_main3LargeAnalyticIntrinsicSurfaceCoefficientHeight_le
      htheta hY hi
  have hbLe : b ≤ B := by
    dsimp [b]
    have hsplit := data.degree_split
    omega
  have hbOnePos : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hBOneLe : (b : ℝ) + 1 ≤ (B : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hbLe
  have hdegreeLog : Real.log ((b : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1) :=
    Real.log_le_log hbOnePos hBOneLe
  have hrawPosNat : 0 < Hraw := by
    dsimp [Hraw]
    exact main3LargeAnalyticIntrinsicEliminantRawHeight_pos
      htheta hY hi key cell data
  have hrawPos : (0 : ℝ) < Hraw := by exact_mod_cast hrawPosNat
  have hrawOne : (1 : ℝ) ≤ Hraw := by exact_mod_cast hrawPosNat
  have hrawCast : (Hraw : ℝ) =
      6 * ((b : ℝ) + 1) * (c : ℝ) * (HF : ℝ) ^ 2 * (HG : ℝ) := by
    dsimp [Hraw, b, c, HF, HFreal, HG,
      main3LargeAnalyticIntrinsicEliminantRawHeight]
    push_cast
    ring
  have hlogRaw : Real.log (Hraw : ℝ) =
      Real.log 6 + Real.log ((b : ℝ) + 1) + Real.log (c : ℝ) +
        2 * Real.log (HF : ℝ) + Real.log (HG : ℝ) := by
    rw [hrawCast]
    rw [Real.log_mul (by positivity) hHGPos.ne',
      Real.log_mul (by positivity) (pow_ne_zero _ hHFpos.ne'),
      Real.log_mul (by positivity) hcPos.ne',
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hbOnePos.ne',
      Real.log_pow]
    ring
  have hrawAdd :
      Real.log ((Hraw : ℝ) + 1) ≤ Real.log 2 + Real.log (Hraw : ℝ) := by
    calc
      Real.log ((Hraw : ℝ) + 1) ≤ Real.log (2 * (Hraw : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log (Hraw : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hrawPos.ne']
  rw [hlogRaw] at hrawAdd
  rw [main3LargeAnalyticIntrinsicEliminantRawLogMajorant]
  linarith

/-- Complete coefficient-height ledger after a binary integral substitution
whose entries have absolute value at most `L`. -/
def main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L : ℝ) : ℝ :=
  let d := main3LargeAnalyticIntrinsicEliminantDegree data
  Real.log ((d : ℝ) + 1) +
    main3LargeAnalyticIntrinsicEliminantRawLogMajorant theta Y B +
      (d : ℝ) * (Real.log 2 + Real.log (L + 1))

/-- The logarithm of the literal post-substitution natural coefficient
height is bounded by the explicit substitution ledger. -/
theorem log_main3LargeAnalyticIntrinsicEliminantSubstitutionHeight_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L : ℝ) (hL : 0 ≤ L) :
    Real.log (main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
      htheta hY hi key cell data L : ℝ) ≤
        main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant data L := by
  let d : ℕ := main3LargeAnalyticIntrinsicEliminantDegree data
  let Hraw : ℕ := main3LargeAnalyticIntrinsicEliminantRawHeight
    htheta hY hi key cell data
  have hrawNonneg : (0 : ℝ) ≤ Hraw := by positivity
  have hbase :
      Real.log (binaryLinearSubstitutionNatHeight d (Hraw : ℝ) L : ℝ) ≤
        Real.log ((d : ℝ) + 1) + Real.log ((Hraw : ℝ) + 1) +
          (d : ℝ) * (Real.log 2 + Real.log (L + 1)) :=
    log_binaryLinearSubstitutionNatHeight_le d hrawNonneg hL
  have hrawLog : Real.log ((Hraw : ℝ) + 1) ≤
      main3LargeAnalyticIntrinsicEliminantRawLogMajorant theta Y B := by
    dsimp [Hraw]
    exact log_main3LargeAnalyticIntrinsicEliminantRawHeight_add_one_le
      htheta hY hi key cell hnonempty hkey data
  rw [main3LargeAnalyticIntrinsicEliminantSubstitutionHeight]
  change Real.log (binaryLinearSubstitutionNatHeight d (Hraw : ℝ) L : ℝ) ≤ _
  rw [main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant]
  dsimp only [d]
  linarith

/-- Value-height numerator used in the first logarithmic sieve budget. -/
def main3LargeAnalyticIntrinsicEliminantValueLogMajorant
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L U V : ℝ) : ℝ :=
  let d := main3LargeAnalyticIntrinsicEliminantDegree data
  Real.log ((d : ℝ) + 1) +
    main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant data L +
      (d : ℝ) * Real.log (4 * (U + V))

/-- Uniform certificate-height numerator used in the second logarithmic
sieve budget. -/
def main3LargeAnalyticIntrinsicEliminantCertificateLogMajorant
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L : ℝ) : ℝ :=
  fullCellCertificateUniformLogMajorant
    (main3LargeAnalyticIntrinsicEliminantDegree data)
    (main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant data L)

/-- One exact maximum threshold for the two logarithmic budgets. -/
def main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L U V : ℝ) : ℝ :=
  max
    (main3LargeAnalyticIntrinsicEliminantValueLogMajorant data L U V /
      (Real.log 2 / 16))
    (main3LargeAnalyticIntrinsicEliminantCertificateLogMajorant data L /
      (Real.log 2 / 8))

/-- A sieve scale above the explicit maximum threshold supplies verbatim the
value-height and universal odd-degree certificate-height hypotheses consumed
by `eventually_fullCell_oddHomogeneousPolynomial_filter_le`. -/
theorem main3LargeAnalyticIntrinsicEliminantSieveBudgets_of_threshold_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    (L U V : ℝ) (sieveN : ℕ)
    (hL : 0 ≤ L) (hU : 0 < U) (hV : 0 < V)
    (hthreshold :
      main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold data L U V ≤
        (sieveN : ℝ)) :
    let d : ℕ := main3LargeAnalyticIntrinsicEliminantDegree data
    let HK : ℕ := main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
      htheta hY hi key cell data L
    let HJ : ℕ := 2 ^ d * (d + 1) * HK
    let Wval : ℝ :=
      ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
    Real.log Wval ≤ (Real.log 2 / 16) * (sieveN : ℝ) ∧
      ∀ j : ℕ, Odd j → 0 < j → j ≤ d →
        fullCellCertificateLogMajorant d HK j + 2 * Real.log (HJ : ℝ) ≤
          (Real.log 2 / 8) * (sieveN : ℝ) := by
  dsimp only
  let d : ℕ := main3LargeAnalyticIntrinsicEliminantDegree data
  let HK : ℕ := main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
    htheta hY hi key cell data L
  let Klog : ℝ :=
    main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant data L
  let HJ : ℕ := 2 ^ d * (d + 1) * HK
  let C : ℝ := 4 * (U + V)
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * C ^ d
  let valueLog : ℝ :=
    Real.log ((d : ℝ) + 1) + Klog + (d : ℝ) * Real.log C
  let certificateLog : ℝ := fullCellCertificateUniformLogMajorant d Klog
  have hd : 0 < d := by
    dsimp [d, main3LargeAnalyticIntrinsicEliminantDegree]
    omega
  have hHKpos : 0 < HK := by
    dsimp [HK]
    exact main3LargeAnalyticIntrinsicEliminantSubstitutionHeight_pos
      htheta hY hi key cell data L
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogHK : Real.log (HK : ℝ) ≤ Klog := by
    dsimp [HK, Klog]
    exact log_main3LargeAnalyticIntrinsicEliminantSubstitutionHeight_le
      htheta hY hi key cell hnonempty hkey data L hL
  have hactual := fullCell_actual_logs_le_of_log_coefficientHeight_le
    d HK C Klog hd hHKpos hC hlogHK
  have hactual' :
      Real.log Wval ≤ valueLog ∧
        ∀ j : ℕ, Odd j → 0 < j → j ≤ d →
          fullCellCertificateLogMajorant d HK j + 2 * Real.log (HJ : ℝ) ≤
            certificateLog := by
    simpa only [HJ, Wval, valueLog, certificateLog] using hactual
  have hthreshold' :
      max (valueLog / (Real.log 2 / 16))
          (certificateLog / (Real.log 2 / 8)) ≤ (sieveN : ℝ) := by
    simpa only [main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold,
      main3LargeAnalyticIntrinsicEliminantValueLogMajorant,
      main3LargeAnalyticIntrinsicEliminantCertificateLogMajorant,
      d, Klog, C, valueLog, certificateLog] using hthreshold
  have hvalueDiv : valueLog / (Real.log 2 / 16) ≤ (sieveN : ℝ) :=
    (le_max_left _ _).trans hthreshold'
  have hcertificateDiv :
      certificateLog / (Real.log 2 / 8) ≤ (sieveN : ℝ) :=
    (le_max_right _ _).trans hthreshold'
  have hvalueBudget :
      valueLog ≤ (Real.log 2 / 16) * (sieveN : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < Real.log 2 / 16)).mp hvalueDiv
    simpa only [mul_comm] using h
  have hcertificateBudget :
      certificateLog ≤ (Real.log 2 / 8) * (sieveN : ℝ) := by
    have h :=
      (div_le_iff₀ (by positivity : 0 < Real.log 2 / 8)).mp hcertificateDiv
    simpa only [mul_comm] using h
  constructor
  · simpa only [Wval, C] using hactual'.1.trans hvalueBudget
  · intro j hj hjpos hjle
    simpa only [HJ] using
      (hactual'.2 j hj hjpos hjle).trans hcertificateBudget

end


end PellPaper
