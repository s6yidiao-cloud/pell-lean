import Pell.Main3LargeAnalyticRealCellRateLedger
import Mathlib.Tactic

/-!
# Public bounds for the normalized real target coordinate

The real-cell rate ledger already proves the normalized source geometry and
the endpoint error estimate used internally by later radial arguments.  This
module exposes their elementary consequence: on every literal real cell, the
normalized target coordinate lies in `[1/2, 2]`.

No lattice reduction, counting, or analytic input is used.
-/

namespace PellPaper

noncomputable section

/-- On a literal real cell, the normalized target coordinate is bounded below
by `1/2` and above by `2`. -/
theorem main3LargeAnalytic_realCellCoordinatePointImage_normalizedTarget_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    (1 / 2 : ℝ) ≤
        main3LargeAnalyticRealCellNormalizedTarget hi ha cell z ∧
      main3LargeAnalyticRealCellNormalizedTarget hi ha cell z ≤ 2 := by
  let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
  let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
  let eps := (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (N : ℝ)
  have hgeometry :=
    main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
      htheta hY hi key cell ha hz
  have hSone : 1 ≤ S := by
    simpa only [S] using hgeometry.2.1
  have hSpos : 0 < S := zero_lt_one.trans_le hSone
  have hSupperRaw :
      S ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) := by
    simpa only [S] using hgeometry.2.2.1
  have heps : eps ≤ 1 / 3 := by
    simpa only [eps] using
      main3LargeAnalytic_realCell_endpoint_error_le_one_third htheta hY hi
  have herror : |T / S ^ 2 - 1| ≤ eps := by
    simpa only [S, T, eps] using
      main3LargeAnalytic_realCellCoordinatePointImage_normalized_ratio_error_le_endpoint
        htheta hY hi key cell ha hz
  have herr := abs_le.mp herror
  have hratioLower : (2 / 3 : ℝ) ≤ T / S ^ 2 := by linarith
  have hratioUpper : T / S ^ 2 ≤ (4 / 3 : ℝ) := by linarith
  have hSsqLower : (1 : ℝ) ≤ S ^ 2 := by nlinarith
  have hTLower : (1 / 2 : ℝ) ≤ T := by
    have hmul : (2 / 3 : ℝ) * S ^ 2 ≤ T :=
      (le_div_iff₀ (sq_pos_of_pos hSpos)).mp hratioLower
    nlinarith
  have hM : (6 : ℝ) ≤ main3UnbalancedM theta Y := by
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hInvM : 1 / (main3UnbalancedM theta Y : ℝ) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) hM
  have hSUpper : S ≤ (7 / 6 : ℝ) := by linarith
  have hSsqUpper : S ^ 2 ≤ (7 / 6 : ℝ) ^ 2 := by nlinarith
  have hTUpper : T ≤ 2 := by
    have hmul : T ≤ (4 / 3 : ℝ) * S ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hSpos)).mp hratioUpper
    calc
      T ≤ (4 / 3 : ℝ) * S ^ 2 := hmul
      _ ≤ (4 / 3 : ℝ) * (7 / 6 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hSsqUpper (by norm_num)
      _ ≤ 2 := by norm_num
  exact ⟨hTLower, hTUpper⟩

end

end PellPaper
