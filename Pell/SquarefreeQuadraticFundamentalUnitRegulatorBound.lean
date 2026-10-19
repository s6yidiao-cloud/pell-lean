import Pell.MaximalOrderFundamentalUnitRegulatorLower
import Pell.SquarefreeQuadraticFundamentalUnitTransport

/-!
# Regulator denominator for a squarefree quadratic presentation

The positive fundamental index attached to a squarefree radicand is either
the radicand itself or four times that radicand, so it never decreases the
underlying scale.  Combining this observation with the existing strict
`1 / 12` lower bound for the normalized maximal-order regulator gives the
literal lower bound on the logarithm of the selected fundamental unit used in
the main3 unit-orbit count.

The scale comparison `Y ≤ w` is kept explicit.  This module does not choose a
squarefree-kernel witness and makes no analytic estimate.
-/

namespace PellPaper

noncomputable section

/-- Passing from a radicand to its positive fundamental index does not
decrease it. -/
theorem le_squarefreeQuadraticFundamentalIndex (w : ℕ) :
    w ≤ squarefreeQuadraticFundamentalIndex w := by
  unfold squarefreeQuadraticFundamentalIndex
  split
  · exact le_rfl
  · omega

/-- If `Y` is at most the squarefree radicand `w`, then the logarithm of the
concretely selected fundamental unit at the associated positive fundamental
index is strictly larger than `log Y / 12`.

Only `1 < Y` is needed; the main3 application has the stronger hypothesis
`65536 ≤ Y`. -/
theorem log_div_twelve_lt_log_concreteFundamentalUnitRealModel
    {Y w : ℕ} (hY : 1 < Y) (hw : Squarefree w) (hwone : 1 < w)
    (hYw : Y ≤ w) :
    let Dfund := squarefreeQuadraticFundamentalIndex w
    let hDfund : PositiveFundamentalDiscriminant Dfund :=
      squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
        w hw hwone
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (Dfund : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
        hDfund⟩
    Real.log (Y : ℝ) / 12 <
      Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta := by
  let Dfund := squarefreeQuadraticFundamentalIndex w
  let hDfund : PositiveFundamentalDiscriminant Dfund :=
    squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
      w hw hwone
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (Dfund : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
      hDfund⟩
  dsimp only
  have hYDfund : Y ≤ Dfund :=
    hYw.trans (le_squarefreeQuadraticFundamentalIndex w)
  have hYDfundReal : (Y : ℝ) ≤ (Dfund : ℝ) := by
    exact_mod_cast hYDfund
  have hYReal : 0 < (Y : ℝ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hDfundReal : 1 < (Dfund : ℝ) := by
    exact_mod_cast hDfund.1
  have hlogMono : Real.log (Y : ℝ) ≤ Real.log (Dfund : ℝ) :=
    Real.log_le_log hYReal hYDfundReal
  have hlogDfund : 0 < Real.log (Dfund : ℝ) :=
    Real.log_pos hDfundReal
  have hregulator :=
    one_div_twelve_lt_maximalOrderFundamentalUnitRegulator hDfund
  rw [maximalOrderFundamentalUnitRegulator_eq_log_of_positiveFundamentalDiscriminant
    hDfund] at hregulator
  have hscaled :
      (1 / 12 : ℝ) * Real.log (Dfund : ℝ) <
        Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta :=
    (lt_div_iff₀ hlogDfund).mp hregulator
  calc
    Real.log (Y : ℝ) / 12 ≤ Real.log (Dfund : ℝ) / 12 := by
      gcongr
    _ = (1 / 12 : ℝ) * Real.log (Dfund : ℝ) := by ring
    _ < Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta := hscaled

end

end PellPaper
