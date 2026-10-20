import Pell.SquarePartExponentSlack

/-!
# The small-root budget

The square-part argument in `main.tex` takes
`s ≤ Y^(λ / (θ + 1))` and chooses `λ` so that raising this inequality to
the exponent `2θ + 1/2` costs at most `Y^(1/4)`.  This file isolates that
elementary real-power calculation.  It contains no counting, determinant, or
square-sieve assertion.
-/

namespace PellPaper

/-- The direct small-root budget used in the square-part range. -/
theorem rpow_le_rpow_quarter_of_small_root_budget
    {θ Y s lam : ℝ} (hθ : 0 ≤ θ) (hY : 1 ≤ Y) (hs : 0 ≤ s)
    (hsmall : s ≤ Y ^ (lam / (θ + 1)))
    (hbudget : (2 * θ + (1 : ℝ) / 2) * (lam / (θ + 1)) ≤ (1 : ℝ) / 4) :
    s ^ (2 * θ + (1 : ℝ) / 2) ≤ Y ^ ((1 : ℝ) / 4) := by
  have hexponent : 0 ≤ 2 * θ + (1 : ℝ) / 2 := by linarith
  calc
    s ^ (2 * θ + (1 : ℝ) / 2) ≤
        (Y ^ (lam / (θ + 1))) ^ (2 * θ + (1 : ℝ) / 2) :=
      Real.rpow_le_rpow hs hsmall hexponent
    _ = Y ^ ((lam / (θ + 1)) * (2 * θ + (1 : ℝ) / 2)) := by
      rw [← Real.rpow_mul (zero_le_one.trans hY)]
    _ ≤ Y ^ ((1 : ℝ) / 4) := by
      apply Real.rpow_le_rpow_of_exponent_le hY
      simpa [mul_comm] using hbudget

/-- Combining the small-root budget with the elementary scale comparison
produces exactly the square-part slack needed for the transfer to a squarefree
radicand. -/
theorem square_part_slack_of_small_root_budget
    {Y s w θ lam : ℝ} (hθ : 0 ≤ θ) (hY : 1 ≤ Y) (hs : 0 < s)
    (hw : 0 ≤ w) (hscale : Y ≤ s ^ 2 * w)
    (hsmall : s ≤ Y ^ (lam / (θ + 1)))
    (hbudget : (2 * θ + (1 : ℝ) / 2) * (lam / (θ + 1)) ≤ (1 : ℝ) / 4) :
    s ^ (2 * θ) ≤ w ^ ((1 : ℝ) / 4) := by
  apply square_part_slack_of_scale_budget (zero_le_one.trans hY) hs hw hscale
  exact rpow_le_rpow_quarter_of_small_root_budget hθ hY hs.le hsmall hbudget

/-- The sharp algebraic sufficient condition for the small-root exponent
budget.  The denominator is positive as soon as `θ ≥ 0`. -/
theorem small_root_exponent_budget_of_le
    {θ lam : ℝ} (hθ : 0 ≤ θ)
    (hlam : lam ≤ (θ + 1) / (8 * θ + 2)) :
    (2 * θ + (1 : ℝ) / 2) * (lam / (θ + 1)) ≤ (1 : ℝ) / 4 := by
  have hden : 0 < θ + 1 := by linarith
  have hfactor : 0 ≤ 2 * θ + (1 : ℝ) / 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlam hfactor
  calc
    (2 * θ + (1 : ℝ) / 2) * (lam / (θ + 1)) =
        ((2 * θ + (1 : ℝ) / 2) * lam) / (θ + 1) := by ring
    _ ≤ (1 : ℝ) / 4 := (div_le_iff₀ hden).2 <| by
      calc
        (2 * θ + (1 : ℝ) / 2) * lam ≤
            (2 * θ + (1 : ℝ) / 2) * ((θ + 1) / (8 * θ + 2)) := hmul
        _ = ((1 : ℝ) / 4) * (θ + 1) := by
          have hden' : 8 * θ + 2 ≠ 0 := by linarith
          field_simp
          ring

/-- A single absolute choice `λ ≤ 1/8` suffices for every nonnegative
`θ`.  This is the convenient uniform form of the manuscript's parameter
condition. -/
theorem small_root_exponent_budget_of_le_one_eighth
    {θ lam : ℝ} (hθ : 0 ≤ θ) (hlam : lam ≤ (1 : ℝ) / 8) :
    (2 * θ + (1 : ℝ) / 2) * (lam / (θ + 1)) ≤ (1 : ℝ) / 4 := by
  apply small_root_exponent_budget_of_le hθ
  have hden : 0 < 8 * θ + 2 := by linarith
  apply (le_div_iff₀ hden).2
  calc
    lam * (8 * θ + 2) ≤ ((1 : ℝ) / 8) * (8 * θ + 2) :=
      mul_le_mul_of_nonneg_right hlam hden.le
    _ ≤ θ + 1 := by nlinarith

/-- The small-root budget with the uniform sufficient choice
`λ ≤ 1/8`. -/
theorem rpow_le_rpow_quarter_of_small_root_budget_of_le_one_eighth
    {θ Y s lam : ℝ} (hθ : 0 ≤ θ) (hY : 1 ≤ Y) (hs : 0 ≤ s)
    (hsmall : s ≤ Y ^ (lam / (θ + 1)))
    (hlam : lam ≤ (1 : ℝ) / 8) :
    s ^ (2 * θ + (1 : ℝ) / 2) ≤ Y ^ ((1 : ℝ) / 4) := by
  apply rpow_le_rpow_quarter_of_small_root_budget hθ hY hs hsmall
  exact small_root_exponent_budget_of_le_one_eighth hθ hlam

end PellPaper
