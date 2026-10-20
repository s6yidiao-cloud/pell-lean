import Pell.SquareParts
import Pell.Definitions

/-!
# Square-part data for exceptional Pell radicands

An exceptional radicand `m` has a unique positive square-part decomposition
`m = s ^ 2 * w`, with `w > 1` squarefree and nonsquare.  The fundamental Pell
solutions for `w` and `m` satisfy `epsilon_w ≤ epsilon_m ≤ m ^ θ`.

The upper bound retains the original radicand `m`: transferring to the
squarefree part does not by itself give the stronger bound `epsilon_w ≤ w ^ θ`.
-/

namespace PellPaper

/-- A small fundamental solution supplies square-part data and fundamental
solutions for both radicands, with the elementary transfer inequality. -/
theorem exists_square_part_fundamental_data_of_smallFundamentalSolution
    {θ : ℝ} {m : ℕ} (hsmall : SmallFundamentalSolution θ m) :
    ∃ s w : ℕ,
      0 < s ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w ∧ ¬ IsSquare w ∧
        ∃ a : Pell.Solution₁ (w : ℤ), ∃ b : Pell.Solution₁ (m : ℤ),
          Pell.IsFundamental a ∧ Pell.IsFundamental b ∧
            epsilon a ≤ epsilon b ∧ epsilon b ≤ (m : ℝ) ^ θ := by
  obtain ⟨hmpos, hmns⟩ := positive_nonsquare_of_smallFundamentalSolution hsmall
  obtain ⟨s, w, hs, hw, hdecomp, hsf, hwns⟩ :=
    exists_square_part_decomposition_of_not_isSquare hmpos hmns
  have hwpos : 0 < (w : ℤ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hw)
  have hwns_int : ¬ IsSquare (w : ℤ) := by
    simpa only [Int.isSquare_natCast_iff] using hwns
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hwpos hwns_int
  obtain ⟨b, hb, hbsmall⟩ := hsmall
  exact ⟨s, w, hs, hw, hdecomp, hsf, hwns, a, b, ha, hb,
    square_part_transfer_of_decomposition hs hdecomp ha hb, hbsmall⟩

/-- Every exceptional radicand admits the square-part decomposition together
with the fundamental solutions and both inequalities used in the reduction. -/
theorem exists_square_part_fundamental_data_of_mem_exceptionalSet
    {θ : ℝ} {X m : ℕ} (hm : m ∈ exceptionalSet θ X) :
    ∃ s w : ℕ,
      0 < s ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w ∧ ¬ IsSquare w ∧
        ∃ a : Pell.Solution₁ (w : ℤ), ∃ b : Pell.Solution₁ (m : ℤ),
          Pell.IsFundamental a ∧ Pell.IsFundamental b ∧
            epsilon a ≤ epsilon b ∧ epsilon b ≤ (m : ℝ) ^ θ := by
  exact exists_square_part_fundamental_data_of_smallFundamentalSolution
    (mem_exceptionalSet.mp hm).2.2

/-- The square-part pair underlying the exceptional-set reduction is unique,
even when the full fundamental-solution data are included in its predicate. -/
theorem existsUnique_square_part_fundamental_data_of_mem_exceptionalSet
    {θ : ℝ} {X m : ℕ} (hm : m ∈ exceptionalSet θ X) :
    ∃! sw : ℕ × ℕ,
      0 < sw.1 ∧ 1 < sw.2 ∧ m = sw.1 ^ 2 * sw.2 ∧
        Squarefree sw.2 ∧ ¬ IsSquare sw.2 ∧
          ∃ a : Pell.Solution₁ (sw.2 : ℤ), ∃ b : Pell.Solution₁ (m : ℤ),
            Pell.IsFundamental a ∧ Pell.IsFundamental b ∧
              epsilon a ≤ epsilon b ∧ epsilon b ≤ (m : ℝ) ^ θ := by
  obtain ⟨s, w, hs, hw, hdecomp, hsf, hwns, a, b, ha, hb, hab, hbsmall⟩ :=
    exists_square_part_fundamental_data_of_mem_exceptionalSet hm
  refine ⟨(s, w), ⟨hs, hw, hdecomp, hsf, hwns, a, b, ha, hb, hab, hbsmall⟩, ?_⟩
  rintro ⟨s', w'⟩ ⟨hs', hw', hdecomp', hsf', _⟩
  obtain ⟨heqs, heqw⟩ := square_part_decomposition_unique
    hs' (lt_trans Nat.zero_lt_one hw') hs (lt_trans Nat.zero_lt_one hw)
    hdecomp' hdecomp hsf' hsf
  exact Prod.ext heqs heqw

/-- For any supplied square-part decomposition and fundamental solution of
its squarefree radicand, exceptional membership bounds its Pell unit by `m^θ`.
Squarefreeness is unnecessary for this direct consequence of transfer. -/
theorem epsilon_le_rpow_of_square_part_of_mem_exceptionalSet
    {θ : ℝ} {X m s w : ℕ} (hm : m ∈ exceptionalSet θ X)
    (hs : 0 < s) (hdecomp : m = s ^ 2 * w)
    {a : Pell.Solution₁ (w : ℤ)} (ha : Pell.IsFundamental a) :
    epsilon a ≤ (m : ℝ) ^ θ := by
  obtain ⟨b, hb, hbsmall⟩ := (mem_exceptionalSet.mp hm).2.2
  exact (square_part_transfer_of_decomposition hs hdecomp ha hb).trans hbsmall

end PellPaper
