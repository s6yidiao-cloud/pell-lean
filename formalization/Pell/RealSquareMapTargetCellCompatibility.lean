import Mathlib.Tactic

/-!
# Finite target-cell compatibility for a perturbed real square map

This module isolates the scalar real-place geometry used by the shifted-square
ratio partition.  If a positive source ratio lies in one multiplicative mesh
window of relative width `1 + 1 / M` and the target/source-square quotient is
within `1 / M` of one, then the normalized target lies between
`1 - 1 / M` and `1 + 7 / M`.  A right-endpoint ceiling therefore assigns the
target to one of nine literal integer cells, independently of every ambient
arithmetic parameter.

No shifted-square package, determinant estimate, or point count is asserted.
-/

namespace PellPaper

noncomputable section

/-- The nine possible target offsets relative to a fixed real source cell. -/
def realSquareMapTargetOffsets : Finset ℤ := Finset.Icc (-1) 7

/-- The right-endpoint target offset after normalizing by the square of the
source-cell centre. -/
def realSquareMapTargetOffset (M s y : ℝ) : ℤ :=
  ⌈M * (y / s ^ 2 - 1)⌉

/-- The target cell indexed by a right-endpoint offset. -/
def realSquareMapTargetCell (M s : ℝ) (k : ℤ) (y : ℝ) : Prop :=
  (k : ℝ) - 1 < M * (y / s ^ 2 - 1) ∧
    M * (y / s ^ 2 - 1) ≤ (k : ℝ)

@[simp]
theorem card_realSquareMapTargetOffsets : realSquareMapTargetOffsets.card = 9 := by
  norm_num [realSquareMapTargetOffsets, Int.card_Icc, Int.toNat_of_nonneg]
  rfl

/-- A positive source window and relative square-map error give an explicit
normalized target interval of width `8 / M`. -/
theorem realSquareMap_targetNormalized_bounds
    {M s x y : ℝ} (hM : 1 ≤ M) (hs : 0 < s) (hx : 0 < x)
    (hy : 0 ≤ y)
    (hwindow : s ≤ x ∧ x ≤ s * (1 + 1 / M))
    (herror : |y / x ^ 2 - 1| ≤ 1 / M) :
    1 - 1 / M ≤ y / s ^ 2 ∧ y / s ^ 2 ≤ 1 + 7 / M := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMinv : 0 ≤ 1 / M := by positivity
  have hMinv_le_one : 1 / M ≤ 1 := by
    exact (div_le_one hMpos).mpr hM
  have herr := (abs_le.mp herror)
  have heLower : 1 - 1 / M ≤ y / x ^ 2 := by linarith
  have heUpper : y / x ^ 2 ≤ 1 + 1 / M := by linarith
  have heNonneg : 0 ≤ y / x ^ 2 := by positivity
  have hqLower : 1 ≤ x / s := by
    exact (le_div_iff₀ hs).mpr (by simpa using hwindow.1)
  have hqUpper : x / s ≤ 1 + 1 / M := by
    exact (div_le_iff₀ hs).mpr (by simpa [mul_comm] using hwindow.2)
  have hqNonneg : 0 ≤ x / s := le_trans (by norm_num) hqLower
  have hfactorLower : 1 ≤ (x / s) ^ 2 := by nlinarith
  have hfactorUpper : (x / s) ^ 2 ≤ (1 + 1 / M) ^ 2 := by nlinarith
  have hbaseNonneg : 0 ≤ 1 - 1 / M := by linarith
  have hupperFactorNonneg : 0 ≤ 1 + 1 / M := by linarith
  have hid : y / s ^ 2 = (y / x ^ 2) * (x / s) ^ 2 := by
    field_simp [hx.ne', hs.ne']
  rw [hid]
  constructor
  · calc
      1 - 1 / M ≤ (1 - 1 / M) * (x / s) ^ 2 := by
        nlinarith [mul_nonneg hbaseNonneg (sub_nonneg.mpr hfactorLower)]
      _ ≤ (y / x ^ 2) * (x / s) ^ 2 :=
        mul_le_mul_of_nonneg_right heLower (sq_nonneg _)
  · calc
      (y / x ^ 2) * (x / s) ^ 2 ≤
          (1 + 1 / M) * (1 + 1 / M) ^ 2 :=
        mul_le_mul heUpper hfactorUpper (sq_nonneg _) hupperFactorNonneg
      _ = (1 + 1 / M) ^ 3 := by ring
      _ ≤ 1 + 7 / M := by
        have htSq : (1 / M) ^ 2 ≤ 1 / M := by nlinarith
        have htCube : (1 / M) ^ 3 ≤ 1 / M := by
          calc
            (1 / M) ^ 3 = (1 / M) * (1 / M) ^ 2 := by ring
            _ ≤ (1 / M) * (1 / M) :=
              mul_le_mul_of_nonneg_left htSq hMinv
            _ = (1 / M) ^ 2 := by ring
            _ ≤ 1 / M := htSq
        calc
          (1 + 1 / M) ^ 3 =
              1 + 3 * (1 / M) + 3 * (1 / M) ^ 2 + (1 / M) ^ 3 := by ring
          _ ≤ 1 + 3 * (1 / M) + 3 * (1 / M) + 1 / M := by gcongr
          _ = 1 + 7 / M := by ring

/-- The normalized target is assigned to its literal right-endpoint cell. -/
theorem realSquareMapTargetOffset_mem_cell
    {M s y : ℝ} :
    realSquareMapTargetCell M s (realSquareMapTargetOffset M s y) y := by
  unfold realSquareMapTargetCell realSquareMapTargetOffset
  constructor
  · have h := Int.ceil_lt_add_one (M * (y / s ^ 2 - 1))
    linarith
  · exact Int.le_ceil _

/-- The explicit normalized interval forces the right-endpoint offset into
the fixed nine-element set `[-1,7]`. -/
theorem realSquareMapTargetOffset_mem_offsets_of_bounds
    {M s y : ℝ} (hM : 1 ≤ M)
    (hbounds : 1 - 1 / M ≤ y / s ^ 2 ∧ y / s ^ 2 ≤ 1 + 7 / M) :
    realSquareMapTargetOffset M s y ∈ realSquareMapTargetOffsets := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have htLower : (-1 : ℝ) ≤ M * (y / s ^ 2 - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hbounds.1 hMpos.le
    have hleft : M * (1 - 1 / M) = M - 1 := by field_simp
    rw [hleft] at hmul
    nlinarith
  have htUpper : M * (y / s ^ 2 - 1) ≤ (7 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hbounds.2 hMpos.le
    have hright : M * (1 + 7 / M) = M + 7 := by field_simp
    rw [hright] at hmul
    nlinarith
  apply Finset.mem_Icc.mpr
  constructor
  · have hreal : (-1 : ℝ) ≤
        (realSquareMapTargetOffset M s y : ℝ) :=
      htLower.trans (by
        simpa [realSquareMapTargetOffset] using
          Int.le_ceil (M * (y / s ^ 2 - 1)))
    exact_mod_cast hreal
  · have hceil : (realSquareMapTargetOffset M s y : ℝ) <
        M * (y / s ^ 2 - 1) + 1 := by
      simpa [realSquareMapTargetOffset] using
        Int.ceil_lt_add_one (M * (y / s ^ 2 - 1))
    have hlt : (realSquareMapTargetOffset M s y : ℝ) < 8 := by linarith
    have hltInt : realSquareMapTargetOffset M s y < (8 : ℤ) := by
      exact_mod_cast hlt
    omega

/-- Capstone: every perturbed real square-map target arising from one source
mesh window belongs to one of exactly nine target cells. -/
theorem exists_realSquareMapTargetOffset_mem_of_sourceWindow
    {M s x y : ℝ} (hM : 1 ≤ M) (hs : 0 < s) (hx : 0 < x)
    (hy : 0 ≤ y)
    (hwindow : s ≤ x ∧ x ≤ s * (1 + 1 / M))
    (herror : |y / x ^ 2 - 1| ≤ 1 / M) :
    ∃ k ∈ realSquareMapTargetOffsets, realSquareMapTargetCell M s k y := by
  refine ⟨realSquareMapTargetOffset M s y, ?_, ?_⟩
  · exact realSquareMapTargetOffset_mem_offsets_of_bounds hM
      (realSquareMap_targetNormalized_bounds hM hs hx hy hwindow herror)
  · exact realSquareMapTargetOffset_mem_cell

end

end PellPaper
