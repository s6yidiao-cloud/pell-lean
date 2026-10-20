import Pell.Main3UnbalancedEnlargedDirectActiveBlockBound
import Pell.Main3UnbalancedEnlargedIndexCount
import Mathlib.Tactic

/-!
# Summing the enlarged main3 direct unbalanced range

The per-block direct estimate retains the varying factors

`7 * sqrt Y + 3 * N / sqrt Y`

and `1 + log (2D)`.  On the direct active family, the first is bounded by
the manuscript `N` threshold and the second by the enlarged Pell height
`ceil ((2Y)^(theta+1/4))`.  This module proves both uniformizations and then
sums the common envelope using the canonical direct-index cardinality.

The sole analytic input remains the transparent textbook proposition
`ShiftedSquareCongruenceWindowAverageAssertion`.  No large-`N` unbalanced
estimate or whole-route aggregation is introduced.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Dividing the direct `N` threshold by `sqrt Y` gives the exact direct
summation exponent. -/
theorem main3UnbalancedEnlargedDirectNThreshold_div_sqrt_eq_rpow
    (theta : ℝ) {Y : ℕ} (hY : 1 ≤ Y) :
    main3UnbalancedEnlargedDirectNThreshold theta Y /
        Real.sqrt (Y : ℝ) =
      (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) := by
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  unfold main3UnbalancedEnlargedDirectNThreshold
  calc
    (Y : ℝ) ^ ((3 : ℝ) / 2 - 1 / (32 * theta ^ 2)) /
        Real.sqrt (Y : ℝ) =
      (Y : ℝ) ^ ((3 : ℝ) / 2 - 1 / (32 * theta ^ 2)) /
        (Y : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
    _ = (Y : ℝ) ^
        (((3 : ℝ) / 2 - 1 / (32 * theta ^ 2)) - (1 : ℝ) / 2) :=
      (Real.rpow_sub hYpos _ _).symm
    _ = (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) := by
      congr 1
      ring

/-- Every enlarged active index has a logarithmic block factor bounded
uniformly by the enlarged height exponent.  The radius and activity filter
retain the original analytic `theta`; only the factor height uses
`theta + 1/4`. -/
theorem main3UnbalancedEnlargedActiveIndex_logFactor_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y) :
    1 + Real.log (2 * (D : ℝ)) ≤
      2 * (theta + 1) *
        (1 + Real.log (((2 * Y : ℕ) : ℝ))) := by
  have hi' := mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hi
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta hY hi'.1 hi'.2
  let x : ℝ := ((2 * Y : ℕ) : ℝ)
  let a : ℝ := theta + 1 / 4
  let z : ℝ := x ^ a
  let H : ℕ := dyadicFactorHeight (theta + 1 / 4) Y
  have hx : (4 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.mul_le_mul_left 2 hY
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have haone : (1 : ℝ) ≤ a := by
    dsimp [a]
    linarith
  have hzfour : (4 : ℝ) ≤ z := by
    calc
      (4 : ℝ) ≤ x := hx
      _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ a := Real.rpow_le_rpow_of_exponent_le hxone haone
      _ = z := rfl
  have hceil : (H : ℝ) < z + 1 := by
    dsimp [H, dyadicFactorHeight, z, x, a]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have hDleH : (D : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast hendpoints.2.2.1
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hendpoints.1
  have hzQuadratic : 0 ≤ (z - 3) * (z + 1) :=
    mul_nonneg (sub_nonneg.mpr (by linarith)) (by linarith)
  have htwoD : 2 * (D : ℝ) ≤ z ^ 2 := by
    nlinarith
  have hlogBound :
      Real.log (2 * (D : ℝ)) ≤ 2 * a * Real.log x := by
    calc
      Real.log (2 * (D : ℝ)) ≤ Real.log (z ^ 2) :=
        Real.log_le_log (by positivity) htwoD
      _ = 2 * Real.log z := by rw [Real.log_pow]; norm_num
      _ = 2 * a * Real.log x := by
        rw [show Real.log z = a * Real.log x by
          dsimp [z]
          exact Real.log_rpow hxpos a]
        ring
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have haUpper : a ≤ theta + 1 := by
    dsimp [a]
    norm_num
  have haLog : a * Real.log x ≤ (theta + 1) * Real.log x :=
    mul_le_mul_of_nonneg_right haUpper hlogx0
  have hthetaOne : (1 : ℝ) ≤ 2 * (theta + 1) := by linarith
  have hfinal :
      1 + Real.log (2 * (D : ℝ)) ≤
        2 * (theta + 1) * (1 + Real.log x) := by
    nlinarith
  simpa only [x] using hfinal

/-- One constant from the congruence-window input bounds every direct active
block by a common endpoint-and-log envelope. -/
theorem main3UnbalancedEnlargedDirectBlock_uniform_bound_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        3 ≤ theta → 2 ≤ Y →
        (h, v, D, N) ∈
          main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y →
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) ≤
          C * ((7 * Real.sqrt (Y : ℝ) +
              3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2))) *
            (2 * (theta + 1) *
              (1 + Real.log (((2 * Y : ℕ) : ℝ))))) := by
  obtain ⟨C, hC, hblock⟩ :=
    main3UnbalancedEnlargedDirectActiveBlockBound_of_congruenceWindowAverage
      haverage
  refine ⟨C, hC, ?_⟩
  intro theta Y h v D N htheta hY hi
  have hiDirect :=
    mem_main3UnbalancedEnlargedDirectDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiDirect.1
  have hbase := hblock theta Y h v D N htheta hY hiActive.1 hiActive.2
  have hYpos : (0 : ℝ) < (Y : ℝ) := by positivity
  have hsqrtYpos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  have hNdiv :
      (N : ℝ) / Real.sqrt (Y : ℝ) ≤
        (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) := by
    calc
      (N : ℝ) / Real.sqrt (Y : ℝ) ≤
          main3UnbalancedEnlargedDirectNThreshold theta Y /
            Real.sqrt (Y : ℝ) :=
        (div_le_div_iff_of_pos_right hsqrtYpos).2 hiDirect.2
      _ = (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) :=
        main3UnbalancedEnlargedDirectNThreshold_div_sqrt_eq_rpow
          theta (by omega)
  have hsource :
      7 * Real.sqrt (Y : ℝ) +
          3 * (N : ℝ) / Real.sqrt (Y : ℝ) ≤
        7 * Real.sqrt (Y : ℝ) +
          3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) := by
    calc
      7 * Real.sqrt (Y : ℝ) +
          3 * (N : ℝ) / Real.sqrt (Y : ℝ) =
        7 * Real.sqrt (Y : ℝ) +
          3 * ((N : ℝ) / Real.sqrt (Y : ℝ)) := by ring
      _ ≤ 7 * Real.sqrt (Y : ℝ) +
          3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) :=
        add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hNdiv (show (0 : ℝ) ≤ 3 by norm_num))
  have hlog :=
    main3UnbalancedEnlargedActiveIndex_logFactor_le htheta hY hiDirect.1
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta hY hiActive.1 hiActive.2
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hendpoints.1
  have hlogFactor0 : 0 ≤ 1 + Real.log (2 * (D : ℝ)) := by
    have hlog0 : 0 ≤ Real.log (2 * (D : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    linarith
  have hsourceMax0 :
      0 ≤ 7 * Real.sqrt (Y : ℝ) +
        3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) := by
    positivity
  have hshape :
      (7 * Real.sqrt (Y : ℝ) +
          3 * (N : ℝ) / Real.sqrt (Y : ℝ)) *
          (1 + Real.log (2 * (D : ℝ))) ≤
        (7 * Real.sqrt (Y : ℝ) +
          3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2))) *
          (2 * (theta + 1) *
            (1 + Real.log (((2 * Y : ℕ) : ℝ)))) :=
    mul_le_mul hsource hlog hlogFactor0 hsourceMax0
  exact hbase.trans (mul_le_mul_of_nonneg_left hshape hC.le)

/-- Complete finite summation of the direct active shifted-square blocks.
The right side is the canonical upper bound for the number of direct indices
times one common per-index envelope.  The existential constant is chosen
before `theta`, `Y`, and the finite family. -/
theorem main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ),
        3 ≤ theta → 2 ≤ Y →
        ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
          ((4 * main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y : ℕ) : ℝ) *
            (C * ((7 * Real.sqrt (Y : ℝ) +
                3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2))) *
              (2 * (theta + 1) *
                (1 + Real.log (((2 * Y : ℕ) : ℝ)))))) := by
  obtain ⟨C, hC, hpoint⟩ :=
    main3UnbalancedEnlargedDirectBlock_uniform_bound_of_congruenceWindowAverage
      haverage
  refine ⟨C, hC, ?_⟩
  intro theta Y htheta hY
  let E : ℝ :=
    C * ((7 * Real.sqrt (Y : ℝ) +
        3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2))) *
      (2 * (theta + 1) *
        (1 + Real.log (((2 * Y : ℕ) : ℝ)))))
  have hsum :
      ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) ≤
        ((main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y).card : ℝ) * E := by
    calc
      ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) =
          ∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            ((squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) := by
        rw [Nat.cast_sum]
      _ ≤ ∑ _i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
          E := by
        apply Finset.sum_le_sum
        intro i hi
        rcases i with ⟨h, v, D, N⟩
        simpa only [E] using hpoint theta Y h v D N htheta hY hi
      _ = ((main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y).card : ℝ) *
          E := by simp
  have hindices :
      ((main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y).card : ℝ) ≤
        ((4 * main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y : ℕ) : ℝ) := by
    exact_mod_cast
      card_main3UnbalancedEnlargedDirectDyadicCoverIndices_le theta Y
  have hxone : (1 : ℝ) ≤ (((2 * Y : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hlog0 : 0 ≤ Real.log (((2 * Y : ℕ) : ℝ)) :=
    Real.log_nonneg hxone
  have hthetaOne0 : 0 ≤ theta + 1 := by linarith
  have hsource0 :
      0 ≤ 7 * Real.sqrt (Y : ℝ) +
        3 * (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) := by
    positivity
  have hlogEnvelope0 :
      0 ≤ 2 * (theta + 1) *
        (1 + Real.log (((2 * Y : ℕ) : ℝ))) := by
    positivity
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg hC.le (mul_nonneg hsource0 hlogEnvelope0)
  have hcounted := mul_le_mul_of_nonneg_right hindices hE0
  exact hsum.trans (by simpa only [E] using hcounted)

end

end PellPaper
