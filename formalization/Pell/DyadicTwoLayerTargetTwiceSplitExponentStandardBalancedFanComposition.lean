import Pell.DyadicTwoLayerFanAggregation
import Pell.TwoLayerTargetTwiceSplitExponentFanRate
import Pell.TwoLayerFanIndex

/-!
# Standard target-twice fan composition with split exponents

The determinant localization exponent and the source-clearing exponent differ
by a fixed logarithmic gap in the intended Pell application.  This isolated
candidate keeps them separate: `qDecay` selects the fan and controls its
weight, while `qCost` is used only in the source endpoint clearing cost.

The Pell-height parameter `cellTheta` is likewise separated from the
near-square numerical parameter `theta`.  It occurs only as the parameter of
the dyadic factor cell passed to the established aggregation theorem.
-/

namespace PellPaper

open Filter

noncomputable section

/-- **Standard numerical target-twice exact-fan bound with separate decay and
clearing exponents.**  The nearest admissible fan index is chosen using
`qDecay`.  The source endpoint product is cleared using `qCost`, and the
resulting excess is charged through the explicit `log 15360` gap. -/
theorem eventually_dyadicFactorBoxCell_card_le_thinFull_of_targetTwiceSplitExponentStandardBalancedFan
    (hWeil : OneVariableQuadraticWeilDegreeBound) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (B H0 : ℕ) (cellTheta theta Q qDecay qCost m : ℝ) (Y : ℕ)
        (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
        (xScale sigma : ℝ),
        0 < M → 2 ≤ Y → 2 ≤ Q →
        3 ≤ theta →
        theta ^ 2 ≤ (B : ℝ) →
        (B : ℝ) < theta ^ 2 + 1 →
        9 / 10 ≤ m → m ≤ 1 →
        m ≤ qDecay → qDecay ≤ 7 * theta / 6 →
        (1 - m) * theta ^ 2 ≤ 1 / 50 →
        Real.exp (800 * theta ^ 2) < (Y : ℝ) →
        (M : ℝ) ≤
          ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (2 * Q) →
        xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
          ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        1536 ≤ xScale → 0 < sigma →
        Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale →
        m * Real.log (Y : ℝ) ≤ Real.log (M : ℝ) →
        qDecay * Real.log (Y : ℝ) =
          (1 - sigma) * Real.log xScale →
        (qCost - qDecay) * Real.log (Y : ℝ) ≤ Real.log 15360 →
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (qCost - 1 / 2) →
        ((2 ^ i.2.2.1 : ℕ) : ℝ) *
            ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) →
        fullCellResidualSieveUniformBudgetThreshold i M B
            (dyadicSourceTargetCellResidualHeight B i) ≤ (N : ℝ) →
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        ((dyadicFactorBoxCell cellTheta Y i).card : ℝ) ≤
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            8 * fullCellOddDegreeSieveAggregateEnvelope
              N (2 * B + 1) U V (M : ℝ) := by
  filter_upwards
    [eventually_dyadicFactorBoxCell_card_le_thinFull_of_twoLayerFan_and_uniformBudget
      hWeil] with N haggregate
  intro B H0 cellTheta theta Q qDecay qCost m Y i M xScale sigma
    hM hY hQ htheta hBlower hBupper hmlower hmupper hmqDecay hqDecay
    hdefect hYgrow hMscale hxQ htargetScale hxScale hsigma
    hlocalThreshold hsourceDecay hxDetL hgap hDE hUV hthreshold
  have hmpos : 0 < m := by linarith
  have hqDecay0 : 0 ≤ qDecay := hmpos.le.trans hmqDecay
  have hlogYpos : 0 < Real.log (Y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 ≤ Real.log (Y : ℝ) := hlogYpos.le
  have hellM : 0 < m * Real.log (Y : ℝ) := mul_pos hmpos hlogYpos
  have hB0 : 0 ≤ (B : ℝ) := by positivity
  have hmB : (9 / 10) * theta ^ 2 ≤ m * (B : ℝ) := by
    calc
      (9 / 10) * theta ^ 2 ≤ (9 / 10) * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hBlower (by norm_num)
      _ ≤ m * (B : ℝ) := mul_le_mul_of_nonneg_right hmlower hB0
  have hqDecayB : qDecay ≤ 2 * m * (B : ℝ) := by
    have hthetaGap : 0 ≤ theta * (theta - 3) := by positivity
    nlinarith
  obtain ⟨fanK, hfanKpos, hfanKB, hfanLower, hfanUpper⟩ :=
    exists_twoLayerFanIndex_scaled B m qDecay (Real.log (Y : ℝ))
      hmpos hlogY hmqDecay hqDecayB
  have hYpos : 0 < (Y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hY)
  have hbaseCost :=
    doubledDyadicSymmetricCost_le_exp_of_sourceRpow_targetTwice
      B i (Y : ℝ) qCost hYpos hDE hUV
  have hrate :=
    twoLayerTargetTwiceSplitExponentFan_rate_of_standardBalanced
      B fanK theta m qDecay qCost (Y : ℝ) htheta hBlower hBupper
      hmlower hmupper hqDecay0 hqDecay hdefect hfanKB hgap hYgrow
  exact haggregate B fanK H0 cellTheta Q Y i M xScale sigma m qDecay
    (Real.log (Y : ℝ))
    (twoLayerTargetTwiceBalancedDoubledBaseLogCost
      B qCost (Real.log (Y : ℝ)))
    hM hY hQ hMscale hxQ htargetScale hxScale hsigma
    hlocalThreshold hsourceDecay hxDetL hellM hfanKpos hfanKB
    hfanLower hfanUpper hbaseCost hrate hthreshold

end

end PellPaper
