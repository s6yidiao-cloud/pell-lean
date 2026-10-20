import Pell.Main3BalancedHighBoxParameters
import Pell.Main3BalancedUniformScale
import Pell.DyadicTwoLayerTargetTwiceSplitExponentBalancedBoxBound
import Mathlib.Tactic

/-!
# Concrete main3 bound for a nonempty high-DE balanced box

This module composes the repaired split-exponent local box theorem with the
literal main3 ceiling, endpoint, high-`DE`, and uniform square-sieve scale
packages.  Every abstract local parameter is thereby eliminated.  The only
mathematical black-box input is the already explicit textbook
`OneVariableQuadraticWeilDegreeBound`.
-/

namespace PellPaper

open Filter

noncomputable section

/-- **Concrete main3 high-box estimate.**  Uniformly in every admissible
growing `theta`, each nonempty actual factor cell in the high-`DE` alternative
satisfies the fully instantiated target-twice balanced local bound. -/
theorem eventually_main3BalancedHighDE_dyadicFactorBoxCell_card_le
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ (theta : ℝ) (i : ℕ × ℕ × ℕ × ℕ),
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        (dyadicFactorBoxCell (theta + 1 / 4) Y i).Nonempty →
        (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
          ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) →
        let B : ℕ := main3BalancedDegree theta
        let H0 : ℕ := 2 * (B + 1)
        let M : ℕ := main3BalancedM theta Y
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        let R : ℝ := dyadicBalancedSquareSieveRealScale i M
        let S : ℝ := Real.sqrt (U * V * (M : ℝ)) + U + V
        ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) +
            327680000000 * ((B : ℝ) + 1) ^ 2 *
              (1 + Real.log (2 * (Y : ℝ))) ^ 3 * R * S := by
  have hlocalEventual :=
    eventually_dyadicFactorBoxCell_card_le_targetTwiceSplitExponentBalancedBox
      hWeil
  obtain ⟨N0, hlocalTail⟩ := eventually_atTop.1 hlocalEventual
  have hlocal := hlocalTail N0 (le_refl N0)
  have hscaleEventual :=
    eventually_main3Balanced_uniform_scale_package c hc hsmall N0
  filter_upwards [hscaleEventual] with Y hscale
  intro theta i htheta hadmissible hcell hhighDE
  let cellTheta : ℝ := theta + 1 / 4
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let Q : ℝ := theta
  let X : ℝ := dyadicTargetEndpointScale i
  let M : ℕ := main3BalancedM theta Y
  let m : ℝ := main3BalancedMLogExponent theta Y
  let qDecay : ℝ := dyadicSplitExponentDecay Y X
  let qCost : ℝ := dyadicSplitExponentCost Y X
  let sigma : ℝ := dyadicSplitExponentSigma X
  have hcell' : (dyadicFactorBoxCell cellTheta Y i).Nonempty := by
    simpa only [cellTheta] using hcell
  obtain ⟨hY, hYgrow, hprime, hN0⟩ :=
    hscale theta cellTheta i htheta hadmissible hcell'
  have hparams :=
    main3BalancedHighBox_parameters theta cellTheta Y i htheta hY
      (by simp only [cellTheta]) hYgrow hcell' (by
        simpa only [cellTheta] using hhighDE)
  rcases hparams with
    ⟨hM, hY', hQ, htheta', hcellTheta, hBlower, hBupper,
      hmlower, hmupper, hmqDecay, hqDecay, hdefect, hYgrow',
      hMscale, hxQ, htargetScale, hxScale, hsigma, hlocalThreshold,
      hsourceDecay, hxDetL, hgap, hDE, _hH0⟩
  have hbound :=
    hlocal B H0 cellTheta theta Q qDecay qCost m Y i M X sigma
      hM hY' hQ htheta' hcellTheta hBlower hBupper hmlower hmupper
      hmqDecay hqDecay hdefect hYgrow' hMscale hxQ htargetScale
      hxScale hsigma hlocalThreshold hsourceDecay hxDetL hgap hDE
      (by simpa only [M] using hprime)
      (by simpa only [M] using hN0)
  simpa only [cellTheta, B, H0, Q, X, M, m, qDecay, qCost, sigma]
    using hbound

end

end PellPaper
