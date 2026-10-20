import Pell.Main3UnbalancedEnlargedShiftedSquareParameters
import Pell.ShiftedSquareCongruenceWindowAverage
import Mathlib.Tactic

/-!
# Direct bounds for enlarged-exponent main3 unbalanced blocks

The transparent textbook congruence-window assertion bounds the exact
shifted-square block by

`C * (N / D + D) * (1 + log (2D))`.

For a nonempty main3 cell at Pell exponent `theta + 1/4`, in the range
`4Y <= N^2` the canonical linear comparability package turns the source
factor into

`N / D + D <= 4 sqrt(Y) + 3 N / sqrt(Y)`.

The small-`N` complement is then controlled directly from the exact scale bounds.
This file proves both numerical cases, transfers the textbook estimate to the
literal source cell, and bounds the complete squarefree block attached to every
active parameter index.  No dyadic sum or project-specific analytic estimate
is assumed.
-/

namespace PellPaper

noncomputable section

/-- In the large-`N` range, the direct shifted-square source cost has an
explicit common form.  All divisions are justified by the positive active
cell endpoints and by `Y >= 2`. -/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_sourceCost_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty)
    (hlarge : 4 * Y ≤ N ^ 2) :
    (N : ℝ) / (D : ℝ) + (D : ℝ) ≤
      4 * Real.sqrt (Y : ℝ) +
        3 * (N : ℝ) / Real.sqrt (Y : ℝ) := by
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta hY hi hcell
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hendpoints.1
  have hYpos : (0 : ℝ) < (Y : ℝ) := by positivity
  have hsqrtYpos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  have hlinear :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_linear_comparability
      htheta hY hi hcell hlarge
  have hNdivD :
      (N : ℝ) / (D : ℝ) ≤ 4 * Real.sqrt (Y : ℝ) := by
    apply (div_le_iff₀ hDpos).2
    nlinarith [hlinear.1]
  have hsqrtFive : Real.sqrt (5 : ℝ) ≤ 3 := by
    have hsqrtFiveSq : Real.sqrt (5 : ℝ) ^ 2 = 5 :=
      Real.sq_sqrt (by norm_num)
    have hsqrtFiveNonneg := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hDdiv :
      (D : ℝ) ≤ Real.sqrt 5 * (N : ℝ) / Real.sqrt (Y : ℝ) := by
    apply (le_div_iff₀ hsqrtYpos).2
    exact hlinear.2
  have hsqrtFiveN :
      Real.sqrt 5 * (N : ℝ) ≤ 3 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hsqrtFive (by positivity)
  have hDthree :
      (D : ℝ) ≤ 3 * (N : ℝ) / Real.sqrt (Y : ℝ) :=
    hDdiv.trans ((div_le_div_iff_of_pos_right hsqrtYpos).2 hsqrtFiveN)
  linarith

/-- The transparent congruence-window average implies one global-constant
pointwise bound for every nonempty active main3 unbalanced cell in the
large-`N` range. -/
theorem main3UnbalancedEnlargedDirectLargeNCellBound_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        3 ≤ theta → 2 ≤ Y →
        (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
          (theta + 1 / 4) Y (main3BalancedR theta Y) →
        (unbalancedShiftedSquareDyadicCoverCell
          (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty →
        4 * Y ≤ N ^ 2 →
        ((unbalancedShiftedSquareDyadicCoverCell
          (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).card : ℝ) ≤
          C * ((4 * Real.sqrt (Y : ℝ) +
              3 * (N : ℝ) / Real.sqrt (Y : ℝ)) *
            (1 + Real.log (2 * (D : ℝ)))) := by
  obtain ⟨C, hC, hblock⟩ :=
    squarefreeShiftedSquareBlock_bound_of_congruenceWindowAverage haverage
  refine ⟨C, hC, ?_⟩
  intro theta Y h v D N htheta hY hi hcell hlarge
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package hi hcell
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta hY hi hcell
  have hDone : 1 ≤ D := by omega
  have hNone : 1 ≤ N := by omega
  have hblockBound := hblock (shiftedSquareA h v) D Y N
    hshift.2.1 hshift.2.2.1 hDone hNone
  have hcellToBlockNat :
      (unbalancedShiftedSquareDyadicCoverCell
        (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).card ≤
        (squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N).card := by
    simpa only [unbalancedShiftedSquareDyadicCoverCell] using
      (card_admissibleUnbalancedShiftedSquareFibre_le_squarefreeBlock
        (theta := theta + 1 / 4) (Y := Y) (R := main3BalancedR theta Y)
        (h := h) (v := v) (D := D) (N := N))
  have hcellToBlock :
      ((unbalancedShiftedSquareDyadicCoverCell
        (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).card : ℝ) ≤
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) := by
    exact_mod_cast hcellToBlockNat
  have hsource :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_sourceCost_le
      htheta hY hi hcell hlarge
  have hDoneReal : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDone
  have hlogFactor : 0 ≤ 1 + Real.log (2 * (D : ℝ)) := by
    have htwoDone : (1 : ℝ) ≤ 2 * (D : ℝ) := by nlinarith
    have hlog0 := Real.log_nonneg htwoDone
    linarith
  have hshape :
      (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
          (1 + Real.log (2 * (D : ℝ)))) ≤
        (4 * Real.sqrt (Y : ℝ) +
            3 * (N : ℝ) / Real.sqrt (Y : ℝ)) *
          (1 + Real.log (2 * (D : ℝ))) :=
    mul_le_mul_of_nonneg_right hsource hlogFactor
  have hscaled := mul_le_mul_of_nonneg_left hshape hC.le
  exact hcellToBlock.trans (hblockBound.trans hscaled)


theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_sourceCost_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty) :
    (N : ℝ) / (D : ℝ) + (D : ℝ) ≤
      7 * Real.sqrt (Y : ℝ) +
        3 * (N : ℝ) / Real.sqrt (Y : ℝ) := by
  by_cases hlarge : 4 * Y ≤ N ^ 2
  · have hbound :=
      nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_sourceCost_le
        htheta hY hi hcell hlarge
    have hsqrt0 : 0 ≤ Real.sqrt (Y : ℝ) := Real.sqrt_nonneg _
    linarith
  · have hscale :=
      nonempty_main3UnbalancedEnlargedShiftedSquareCell_squared_scale_bounds hi hcell
    have hRleNat : main3BalancedR theta Y ≤ Y :=
      (main3BalancedR_parameter_package theta Y htheta hY).2.2.2
    have hRle : (main3BalancedR theta Y : ℝ) ≤ (Y : ℝ) := by
      exact_mod_cast hRleNat
    have hsmallNat : N ^ 2 < 4 * Y := Nat.lt_of_not_ge hlarge
    have hsmall : (N : ℝ) ^ 2 < 4 * (Y : ℝ) := by
      exact_mod_cast hsmallNat
    have hYpos : (0 : ℝ) < (Y : ℝ) := by positivity
    have hsqrtYpos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
    have hsqrtYSq : Real.sqrt (Y : ℝ) ^ 2 = (Y : ℝ) :=
      Real.sq_sqrt hYpos.le
    have hDposNat : 0 < D :=
      (nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
        htheta hY hi hcell).1
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposNat
    have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDposNat
    have hDsq : (D : ℝ) ^ 2 < 18 := by
      have hraw := hscale.1
      nlinarith
    have hDle : (D : ℝ) ≤ 5 := by
      nlinarith [sq_nonneg ((D : ℝ) - 5)]
    have hNle : (N : ℝ) ≤ 2 * Real.sqrt (Y : ℝ) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [sq_nonneg ((N : ℝ) + 2 * Real.sqrt (Y : ℝ))]
    have hsqrtYone : (1 : ℝ) ≤ Real.sqrt (Y : ℝ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast (show 1 ≤ Y by omega)
    have hNdivD : (N : ℝ) / (D : ℝ) ≤ (N : ℝ) := by
      apply (div_le_iff₀ hDpos).2
      nlinarith
    have hDsqrt : (D : ℝ) ≤ 5 * Real.sqrt (Y : ℝ) := by
      nlinarith
    have hextra : 0 ≤ 3 * (N : ℝ) / Real.sqrt (Y : ℝ) := by
      positivity
    linarith

/-- The congruence-window average bounds the complete squarefree
shifted-square block attached to every nonempty active main3 cell, with one
constant chosen before all cell parameters. -/
theorem main3UnbalancedEnlargedDirectActiveBlockBound_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        3 ≤ theta → 2 ≤ Y →
        (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
          (theta + 1 / 4) Y (main3BalancedR theta Y) →
        (unbalancedShiftedSquareDyadicCoverCell
          (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty →
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) ≤
          C * ((7 * Real.sqrt (Y : ℝ) +
              3 * (N : ℝ) / Real.sqrt (Y : ℝ)) *
            (1 + Real.log (2 * (D : ℝ)))) := by
  obtain ⟨C, hC, hblock⟩ :=
    squarefreeShiftedSquareBlock_bound_of_congruenceWindowAverage haverage
  refine ⟨C, hC, ?_⟩
  intro theta Y h v D N htheta hY hi hcell
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package hi hcell
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta hY hi hcell
  have hDone : 1 ≤ D := by omega
  have hNone : 1 ≤ N := by omega
  have hblockBound := hblock (shiftedSquareA h v) D Y N
    hshift.2.1 hshift.2.2.1 hDone hNone
  have hsource :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_sourceCost_le
      htheta hY hi hcell
  have hlogFactor : 0 ≤ 1 + Real.log (2 * (D : ℝ)) := by
    have hDoneReal : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDone
    have htwoDone : (1 : ℝ) ≤ 2 * (D : ℝ) := by nlinarith
    have hlog0 := Real.log_nonneg htwoDone
    linarith
  have hshape := mul_le_mul_of_nonneg_right hsource hlogFactor
  exact hblockBound.trans (mul_le_mul_of_nonneg_left hshape hC.le)


end

end PellPaper
