import Pell.SquarePartExponentSlack

/-!
# Square-part transfer to a general fixed height

A transferred unit bound at `s ^ 2 * w` upgrades from exponent `theta` to any
target exponent `phi` once the square-part slack is at most `w ^ (phi - theta)`.
For `theta ≤ phi`, the scale budget `s ^ (2 * phi) ≤ Y ^ (phi - theta)` supplies
that slack whenever `Y ≤ s ^ 2 * w` and `s` is positive.

The Pell corollaries retain the exact transferred unit bound and give a
pointwise fixed-height conclusion. No counting or power-saving estimate is
asserted.
-/

namespace PellPaper

/-- General fixed-height transfer from explicit square-part exponent slack.
No order condition on the exponents is needed once the slack is supplied. -/
theorem le_rpow_of_square_part_exponent_slack
    {e s w theta phi : ℝ} (hs : 0 ≤ s) (hw : 0 < w)
    (he : e ≤ (s ^ 2 * w) ^ theta)
    (hslack : s ^ (2 * theta) ≤ w ^ (phi - theta)) :
    e ≤ w ^ phi := by
  calc
    e ≤ (s ^ 2 * w) ^ theta := he
    _ = (s ^ 2) ^ theta * w ^ theta :=
      Real.mul_rpow (sq_nonneg s) hw.le
    _ = s ^ (2 * theta) * w ^ theta := by
      rw [square_rpow_eq_rpow_two_mul hs]
    _ ≤ w ^ (phi - theta) * w ^ theta :=
      mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hw.le _)
    _ = w ^ phi := by
      rw [← Real.rpow_add hw]
      congr 1
      ring

/-- A general scale budget yields square-part exponent slack. Positivity of
`s` permits cancellation, and `theta ≤ phi` permits raising the scale
inequality to the exponent `phi - theta`. The scale and radicand may be zero. -/
theorem square_part_exponent_slack_of_scale_budget
    {Y s w theta phi : ℝ} (hY : 0 ≤ Y) (hs : 0 < s) (hw : 0 ≤ w)
    (htheta_phi : theta ≤ phi) (hscale : Y ≤ s ^ 2 * w)
    (hbudget : s ^ (2 * phi) ≤ Y ^ (phi - theta)) :
    s ^ (2 * theta) ≤ w ^ (phi - theta) := by
  have hmain : s ^ (2 * phi) ≤ (s ^ 2 * w) ^ (phi - theta) :=
    hbudget.trans (Real.rpow_le_rpow hY hscale (sub_nonneg.mpr htheta_phi))
  have hleft : s ^ (2 * phi) =
      s ^ (2 * theta) * s ^ (2 * (phi - theta)) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hright : (s ^ 2 * w) ^ (phi - theta) =
      s ^ (2 * (phi - theta)) * w ^ (phi - theta) := by
    rw [Real.mul_rpow (sq_nonneg s) hw,
      square_rpow_eq_rpow_two_mul hs.le]
  rw [hleft, hright] at hmain
  exact le_of_mul_le_mul_right (by simpa only [mul_comm] using hmain)
    (Real.rpow_pos_of_pos hs (2 * (phi - theta)))

/-- Natural-number scale-to-slack transfer, with a positive square-part root
and no positivity assumption on the natural scale or radicand. -/
theorem square_part_exponent_slack_of_nat_scale_budget
    {Y s w : ℕ} {theta phi : ℝ} (hs : 0 < s) (htheta_phi : theta ≤ phi)
    (hscale : Y ≤ s ^ 2 * w)
    (hbudget : (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta)) :
    (s : ℝ) ^ (2 * theta) ≤ (w : ℝ) ^ (phi - theta) := by
  apply square_part_exponent_slack_of_scale_budget (Y := (Y : ℝ))
    (s := (s : ℝ)) (w := (w : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast hs
  · exact Nat.cast_nonneg _
  · exact htheta_phi
  · exact_mod_cast hscale
  · exact hbudget

/-- General fixed-height bound for a Pell unit satisfying the exact
transferred cutoff. Fundamentality is unnecessary for this inequality. -/
theorem epsilon_le_rpow_of_nat_square_part_exponent_slack
    {s w : ℕ} {theta phi : ℝ} {a : Pell.Solution₁ (w : ℤ)}
    (hw : 0 < w)
    (he : epsilon a ≤ ((s ^ 2 * w : ℕ) : ℝ) ^ theta)
    (hslack : (s : ℝ) ^ (2 * theta) ≤ (w : ℝ) ^ (phi - theta)) :
    epsilon a ≤ (w : ℝ) ^ phi := by
  apply le_rpow_of_square_part_exponent_slack
    (s := (s : ℝ)) (w := (w : ℝ))
  · exact Nat.cast_nonneg _
  · exact_mod_cast hw
  · simpa only [Nat.cast_mul, Nat.cast_pow] using he
  · exact hslack

/-- The scale budget upgrades the transferred cutoff for the same Pell unit;
the conclusion does not replace it by a different solution. -/
theorem epsilon_le_rpow_of_nat_square_part_scale_budget
    {Y s w : ℕ} {theta phi : ℝ} {a : Pell.Solution₁ (w : ℤ)}
    (hs : 0 < s) (hw : 0 < w) (htheta_phi : theta ≤ phi)
    (hscale : Y ≤ s ^ 2 * w)
    (he : epsilon a ≤ ((s ^ 2 * w : ℕ) : ℝ) ^ theta)
    (hbudget : (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta)) :
    epsilon a ≤ (w : ℝ) ^ phi := by
  exact epsilon_le_rpow_of_nat_square_part_exponent_slack hw he
    (square_part_exponent_slack_of_nat_scale_budget hs htheta_phi hscale hbudget)

/-- A transferred dyadic witness has fixed height `phi` when its square-part
slack is explicitly bounded by `w ^ (phi - theta)`. -/
theorem smallFundamentalSolution_of_mem_dyadicTransferredSquarefreeSet_of_exponent_slack
    {theta phi : ℝ} {Y s w : ℕ}
    (hmem : w ∈ dyadicTransferredSquarefreeSet theta Y s)
    (hslack : (s : ℝ) ^ (2 * theta) ≤ (w : ℝ) ^ (phi - theta)) :
    SmallFundamentalSolution phi w := by
  obtain ⟨hwlo, _, _, _, _, a, ha, he⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp hmem
  exact ⟨a, ha, epsilon_le_rpow_of_nat_square_part_exponent_slack
    (lt_of_lt_of_le Nat.zero_lt_two hwlo) he hslack⟩

/-- A general scale budget upgrades an ordinary transferred dyadic witness
to fixed height `phi`. The lower scale bound and a positive radicand are
extracted from membership; the root positivity remains explicit. -/
theorem smallFundamentalSolution_of_mem_dyadicTransferredSquarefreeSet_of_height_budget
    {theta phi : ℝ} {Y s w : ℕ} (hs : 0 < s) (htheta_phi : theta ≤ phi)
    (hmem : w ∈ dyadicTransferredSquarefreeSet theta Y s)
    (hbudget : (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta)) :
    SmallFundamentalSolution phi w := by
  obtain ⟨hwlo, _, hscale, _, _, a, ha, he⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp hmem
  exact ⟨a, ha, epsilon_le_rpow_of_nat_square_part_scale_budget hs
    (lt_of_lt_of_le Nat.zero_lt_two hwlo) htheta_phi hscale he hbudget⟩

end PellPaper
