import Pell.DyadicSquarePartReduction

/-!
# The small-square-part exponent slack

The square-part reduction naturally transfers a bound of the form
`epsilon_w ≤ (s^2 w)^theta`.  This file records the elementary exponent
calculation which turns it into a fixed-height bound at the squarefree
radicand once the square-part root satisfies the manuscript's slack
inequality `s^(2 theta) ≤ w^(1/4)`.

It also derives that slack from the scale conditions used in the small-root
range.  These are only real-power identities and order comparisons; no
determinant or counting estimate is asserted here.
-/

namespace PellPaper

/-- Raising a real square to a real power, with the exponent written on the
base.  The nonnegativity condition is precisely what `Real.rpow_mul` needs. -/
theorem square_rpow_eq_rpow_two_mul {s t : ℝ} (hs : 0 ≤ s) :
    (s ^ 2) ^ t = s ^ (2 * t) := by
  rw [← Real.rpow_two s, ← Real.rpow_mul hs]

/-- The basic small-square-part exponent calculation.  A bound at the original
radicand `s^2 w`, together with `s^(2 theta) ≤ w^(1/4)`, gives the fixed-height
bound with the explicit additional exponent `1/4`. -/
theorem le_rpow_add_quarter_of_square_part_slack
    {e s w θ : ℝ} (hs : 0 ≤ s) (hw : 0 < w)
    (he : e ≤ (s ^ 2 * w) ^ θ)
    (hslack : s ^ (2 * θ) ≤ w ^ ((1 : ℝ) / 4)) :
    e ≤ w ^ (θ + (1 : ℝ) / 4) := by
  calc
    e ≤ (s ^ 2 * w) ^ θ := he
    _ = (s ^ 2) ^ θ * w ^ θ := Real.mul_rpow (sq_nonneg s) hw.le
    _ = s ^ (2 * θ) * w ^ θ := by
      rw [square_rpow_eq_rpow_two_mul hs]
    _ ≤ w ^ ((1 : ℝ) / 4) * w ^ θ := by
      exact mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hw.le _)
    _ = w ^ (θ + (1 : ℝ) / 4) := by
      calc
        w ^ ((1 : ℝ) / 4) * w ^ θ = w ^ θ * w ^ ((1 : ℝ) / 4) := mul_comm _ _
        _ = w ^ (θ + (1 : ℝ) / 4) :=
          (Real.rpow_add hw θ ((1 : ℝ) / 4)).symm

/-- The preceding calculation in the integral square-part notation used by
the Pell reduction.  The solution need not be assumed fundamental here: the
statement is solely an inequality for its associated unit. -/
theorem epsilon_le_rpow_add_quarter_of_nat_square_part_slack
    {s w : ℕ} {θ : ℝ} {a : Pell.Solution₁ (w : ℤ)}
    (hw : 0 < w)
    (he : epsilon a ≤ ((s ^ 2 * w : ℕ) : ℝ) ^ θ)
    (hslack : (s : ℝ) ^ (2 * θ) ≤ (w : ℝ) ^ ((1 : ℝ) / 4)) :
    epsilon a ≤ (w : ℝ) ^ (θ + (1 : ℝ) / 4) := by
  apply le_rpow_add_quarter_of_square_part_slack
    (s := (s : ℝ)) (w := (w : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast hw
  · simpa only [Nat.cast_mul, Nat.cast_pow] using he
  · exact hslack

/-- The scale inequalities in the manuscript imply the square-part slack.
The extra `s^(1/2)` in the second hypothesis is exactly cancelled against
`(s^2)^(1/4)`. -/
theorem square_part_slack_of_scale_budget
    {Y s w θ : ℝ} (hY : 0 ≤ Y) (hs : 0 < s) (hw : 0 ≤ w)
    (hscale : Y ≤ s ^ 2 * w)
    (hbudget : s ^ (2 * θ + (1 : ℝ) / 2) ≤ Y ^ ((1 : ℝ) / 4)) :
    s ^ (2 * θ) ≤ w ^ ((1 : ℝ) / 4) := by
  have hquarter : Y ^ ((1 : ℝ) / 4) ≤ (s ^ 2 * w) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hY hscale (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hmain : s ^ (2 * θ + (1 : ℝ) / 2) ≤
      (s ^ 2 * w) ^ ((1 : ℝ) / 4) :=
    hbudget.trans hquarter
  have hleft : s ^ (2 * θ + (1 : ℝ) / 2) =
      s ^ (2 * θ) * s ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_add hs]
  have hright : (s ^ 2 * w) ^ ((1 : ℝ) / 4) =
      s ^ ((1 : ℝ) / 2) * w ^ ((1 : ℝ) / 4) := by
    calc
      (s ^ 2 * w) ^ ((1 : ℝ) / 4) =
          (s ^ 2) ^ ((1 : ℝ) / 4) * w ^ ((1 : ℝ) / 4) :=
        Real.mul_rpow (sq_nonneg s) hw
      _ = s ^ (2 * ((1 : ℝ) / 4)) * w ^ ((1 : ℝ) / 4) := by
        rw [square_rpow_eq_rpow_two_mul hs.le]
      _ = s ^ ((1 : ℝ) / 2) * w ^ ((1 : ℝ) / 4) := by norm_num
  rw [hleft, hright] at hmain
  have hsqrt : 0 < s ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hs _
  apply le_of_mul_le_mul_right (by simpa [mul_comm] using hmain) hsqrt

/-- Natural-number version of the scale-to-slack calculation. -/
theorem square_part_slack_of_nat_scale_budget
    {Y s w : ℕ} {θ : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hscale : Y ≤ s ^ 2 * w)
    (hbudget : (s : ℝ) ^ (2 * θ + (1 : ℝ) / 2) ≤
      (Y : ℝ) ^ ((1 : ℝ) / 4)) :
    (s : ℝ) ^ (2 * θ) ≤ (w : ℝ) ^ ((1 : ℝ) / 4) := by
  apply square_part_slack_of_scale_budget (Y := (Y : ℝ))
    (s := (s : ℝ)) (w := (w : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast hs
  · exact_mod_cast hw.le
  · exact_mod_cast hscale
  · exact hbudget

/-- A transferred dyadic squarefree witness becomes a genuine fixed-height
witness after imposing the explicit square-part slack. -/
theorem smallFundamentalSolution_add_quarter_of_mem_dyadicTransferredSquarefreeSet
    {θ : ℝ} {Y s w : ℕ}
    (hmem : w ∈ dyadicTransferredSquarefreeSet θ Y s)
    (hslack : (s : ℝ) ^ (2 * θ) ≤ (w : ℝ) ^ ((1 : ℝ) / 4)) :
    SmallFundamentalSolution (θ + (1 : ℝ) / 4) w := by
  obtain ⟨hwlo, _, _, _, _, a, ha, he⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp hmem
  refine ⟨a, ha, ?_⟩
  apply le_rpow_add_quarter_of_square_part_slack
    (s := (s : ℝ)) (w := (w : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hwlo)
  · simpa only [Nat.cast_mul, Nat.cast_pow] using he
  · exact hslack

/-- The manuscript's scale budget supplies the preceding slack automatically
for a transferred dyadic squarefree witness. -/
theorem smallFundamentalSolution_add_quarter_of_mem_dyadicTransferredSquarefreeSet_of_budget
    {θ : ℝ} {Y s w : ℕ} (hs : 0 < s)
    (hmem : w ∈ dyadicTransferredSquarefreeSet θ Y s)
    (hbudget : (s : ℝ) ^ (2 * θ + (1 : ℝ) / 2) ≤
      (Y : ℝ) ^ ((1 : ℝ) / 4)) :
    SmallFundamentalSolution (θ + (1 : ℝ) / 4) w := by
  obtain ⟨hwlo, _, hscale, _, _, _, _, _⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp hmem
  apply smallFundamentalSolution_add_quarter_of_mem_dyadicTransferredSquarefreeSet hmem
  exact square_part_slack_of_nat_scale_budget hs
    (lt_of_lt_of_le Nat.zero_lt_two hwlo) hscale hbudget

end PellPaper
