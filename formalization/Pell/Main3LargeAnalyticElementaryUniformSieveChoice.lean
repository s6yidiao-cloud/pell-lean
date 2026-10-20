import Pell.Main3LargeAnalyticElementaryIntrinsicSieveAt
import Pell.Main3LargeAnalyticUniformSieveScale
import Mathlib.Tactic

namespace PellPaper

open Filter

noncomputable section

theorem eventually_main3LargeAnalytic_uniformElementarySieveChoice
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      3 ≤ theta →
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      FullCellElementaryOddHomogeneousPolynomialSieveAt
          (main3LargeAnalyticSieveN theta Y) ∧
        Real.exp (800 * theta ^ 2) < (Y : ℝ) ∧
        4 ≤ main3LargeAnalyticSieveN theta Y ∧
        128000 * theta ^ 7 * Real.log (Y : ℝ) ≤
          (main3LargeAnalyticSieveN theta Y : ℝ) ∧
        (main3LargeAnalyticSieveN theta Y : ℝ) ≤
          2 * (Y : ℝ) ^ (1 / (32 * theta ^ 2)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    eventually_fullCellElementaryOddHomogeneousPolynomialSieveAt
  have hscale :=
    eventually_main3LargeAnalytic_uniformSieveScale_package c hc hsmall N₀
  filter_upwards [hscale] with Y hscaleY
  intro theta htheta hadmissible
  have hpackage := hscaleY theta htheta hadmissible
  exact ⟨hN₀ _ hpackage.2.2.1, hpackage.1, hpackage.2.1,
    hpackage.2.2.2.1, hpackage.2.2.2.2⟩

end

end PellPaper

#print axioms PellPaper.eventually_main3LargeAnalytic_uniformElementarySieveChoice
