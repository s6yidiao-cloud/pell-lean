import Pell.Main3LargeAnalyticTargetFibreLogCount
import Pell.Main3LargeAnalyticTargetFibreFormHeightLogBound
import Pell.QuadraticFormUnitHeightCapacityAbsorption
import Pell.SquarefreeQuadraticFundamentalUnitRegulatorBound
import Mathlib.Tactic

/-!
# Linear-theta count for one literal main3 target fibre

The exact ideal partition and signed-unit height count are combined with the
literal form-height budget and the regulator lower bound.  A nonempty target
fibre supplies its canonical squarefree radicand in `[Y, 2Y)`, while the empty
case is immediate.

The resulting estimate is unconditional and contains no analytic or Weil-bound
premise.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- Once a squarefree presentation of the primitive discriminant has been
chosen with radicand at least `Y`, the literal fixed-target fibre costs at most
`1024 * theta` times the divisor count of the fixed auxiliary-key level. -/
theorem card_main3LargeAnalyticFixedKeyCellTargetFibre_le_1024_mul_theta_mul_key_divisors_of_squarefreeKernel
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y)
    (w s : ℕ) (hw : Squarefree w) (hYw : Y ≤ w)
    (hwone : 1 < w) (hs : 0 < s)
    (hdisc :
      (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ)) :
    ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤
      1024 * theta *
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare
      ((w * s ^ 2 : ℕ) : ℤ) (by
        simpa only [Int.isSquare_natCast_iff] using
          not_isSquare_squarefree_mul_sq hw hwone hs)⟩
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
  let m₀ := shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ)
  let X := main3LargeAnalyticFixedKeySourceCoordinateRadius
    (shiftedSquareA h v) D key
  let H := IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant
    ((w * s ^ 2 : ℕ) : ℤ) Q X
  let A : ℝ := |(Q.a : ℝ) * (m₀ : ℝ)|
  let L := A / H
  let Dfund := squarefreeQuadraticFundamentalIndex w
  let hDfund : PositiveFundamentalDiscriminant Dfund :=
    squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
      w hw hwone
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (Dfund : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
      hDfund⟩
  have hparameters :=
    main3LargeAnalytic_targetFibreLeadingPell_parameters
      htheta hY hi key cell y p₀
  change 0 < Q.discriminant ∧ ¬ IsSquare Q.discriminant ∧ Q.a ≠ 0 ∧
    4 * Q.a * m₀ ≠ 0 at hparameters
  have hproductInt : Q.a * m₀ ≠ 0 := by
    intro hzero
    apply hparameters.2.2.2
    calc
      4 * Q.a * m₀ = 4 * (Q.a * m₀) := by ring
      _ = 0 := by rw [hzero]; ring
  have hA : (1 : ℝ) ≤ A := by
    dsimp only [A]
    have hinter : 1 ≤ |Q.a * m₀| := Int.one_le_abs hproductInt
    exact_mod_cast hinter
  have hX : (1 : ℝ) ≤ X := by
    dsimp only [X]
    exact
      one_le_main3LargeAnalyticFixedKeySourceCoordinateRadius_of_targetFibrePoint
        htheta hY hi key cell y p₀
  have hH : 0 < H := by
    dsimp only [H]
    exact IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant_pos
      ((w * s ^ 2 : ℕ) : ℤ) (by positivity) Q (zero_le_one.trans hX)
  have hlogH : Real.log H ≤ 21 * theta * Real.log (Y : ℝ) := by
    dsimp only [H, Q, X]
    exact
      log_main3LargeAnalyticFixedTargetFormIdealVectorRealHeightMajorant_le
        htheta hY hi key cell y p₀ w s hdisc
  have hlogEta : Real.log (Y : ℝ) / 12 <
      Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta := by
    dsimp only [Dfund, hDfund]
    exact log_div_twelve_lt_log_concreteFundamentalUnitRealModel
      (show 1 < Y by omega) hw hwone hYw
  have hcapacity :
      2 * (1 + Real.log (H / L) /
        Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta) ≤
          1024 * theta := by
    change 2 * (1 + Real.log (H / (A / H)) /
        Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta) ≤
      1024 * theta
    exact two_mul_one_add_reciprocal_height_log_capacity_le_1024_mul_theta
      htheta (show 2 ≤ Y by omega) hH hA hlogH hlogEta
  have hcount :=
    card_main3LargeAnalyticFixedKeyCellTargetFibre_le_key_divisors_mul_log_height
      htheta hY hi key cell y p₀ w s hw hwone hs hdisc
  change
    ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤
      ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) *
        (2 * (1 + Real.log (H / L) /
          Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta)) at hcount
  calc
    ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) *
          (2 * (1 + Real.log (H / L) /
            Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta)) := hcount
    _ ≤ ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) *
          (1024 * theta) := by
      exact mul_le_mul_of_nonneg_left hcapacity (by positivity)
    _ = 1024 * theta *
          ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) := by
      ring

/-- Every literal fixed-key, fixed-cell target fibre has cardinality at most
`1024 * theta` times the divisor count of the auxiliary-key surface level.
The squarefree radicand and its positive square factor are selected internally
from any point of the fibre. -/
theorem card_main3LargeAnalyticFixedKeyCellTargetFibre_le_1024_mul_theta_mul_key_divisors
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :
    ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤
      1024 * theta *
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) := by
  classical
  by_cases hfibre :
      (main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).Nonempty
  · obtain ⟨p, hp⟩ := hfibre
    let p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
        htheta hY hi key cell y := ⟨p, hp⟩
    have hkernel := main3LargeAnalytic_targetFibre_squarefreeKernelData
      htheta hY hi key cell y p₀
    obtain ⟨w, s, hw, hYw, _hwY, hwone, hs, hdisc⟩ := hkernel
    exact
      card_main3LargeAnalyticFixedKeyCellTargetFibre_le_1024_mul_theta_mul_key_divisors_of_squarefreeKernel
        htheta hY hi key cell y p₀ w s hw hYw hwone hs hdisc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hfibre]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hthetaNonneg : 0 ≤ theta := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hthetaNonneg) (by positivity)

end

end PellPaper
