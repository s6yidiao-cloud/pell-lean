import Pell.DyadicBoxReduction
import Pell.ShiftedSquareBlock
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Exact finite dyadic cover of the admissible unbalanced range

An admissible unbalanced factor tuple has one of four signed differences,
a positive oriented factor `v < R`, a positive square coordinate `d` bounded
by `dyadicFactorHeight theta Y`, and a positive shifted-square coordinate
`n = e * v` bounded by `dyadicFactorHeight theta Y * R`.

This file puts `d` and `n` into their exact half-open binary intervals and
covers the whole tuple set by finitely many fixed `(h,v,D,N)` fibres from
`ShiftedSquareBlock`.  It then sums the already-proved fibrewise injections
into squarefree shifted-square blocks.  No analytic estimate is asserted.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The literal four signed differences occurring in the Pell factor
separation. -/
def signedDyadicDifferenceValues : Finset ℤ := {1, -1, 2, -2}

@[simp] theorem mem_signedDyadicDifferenceValues {h : ℤ} :
    h ∈ signedDyadicDifferenceValues ↔ IsSignedDyadicDifference h := by
  simp [signedDyadicDifferenceValues, IsSignedDyadicDifference]

/-- Lower endpoints of the binary intervals required to cover the positive
naturals at most `H`. -/
def dyadicLowerEndpoints (H : ℕ) : Finset ℕ :=
  (Finset.range (dyadicScaleCount H)).image fun k => 2 ^ k

/-- The lower endpoint selected by the binary floor logarithm occurs in the
finite endpoint family at height `H`. -/
theorem pow_log_mem_dyadicLowerEndpoints {n H : ℕ}
    (hn : 0 < n) (hnH : n ≤ H) :
    2 ^ Nat.log 2 n ∈ dyadicLowerEndpoints H := by
  apply Finset.mem_image.mpr
  exact ⟨Nat.log 2 n, log_mem_dyadicScaleRange hn hnH, rfl⟩

/-- Finite fixed-parameter family for the unbalanced shifted-square cover.
The coordinates are the signed difference `h`, the positive factor `v`, and
the literal lower endpoints `D,N` of the half-open binary intervals for
`d` and `n=e*v`. -/
noncomputable def unbalancedShiftedSquareDyadicCoverIndices
    (theta : ℝ) (Y R : ℕ) : Finset (ℤ × ℕ × ℕ × ℕ) :=
  signedDyadicDifferenceValues.product
    ((Finset.Ico 1 R).product
      ((dyadicLowerEndpoints (dyadicFactorHeight theta Y)).product
        (dyadicLowerEndpoints (dyadicFactorHeight theta Y * R))))

@[simp] theorem mem_unbalancedShiftedSquareDyadicCoverIndices
    {theta : ℝ} {Y R : ℕ} {h : ℤ} {v D N : ℕ} :
    (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices theta Y R ↔
      IsSignedDyadicDifference h ∧ 1 ≤ v ∧ v < R ∧
        D ∈ dyadicLowerEndpoints (dyadicFactorHeight theta Y) ∧
        N ∈ dyadicLowerEndpoints (dyadicFactorHeight theta Y * R) := by
  simp [unbalancedShiftedSquareDyadicCoverIndices, and_assoc]

/-- The fixed `(h,v,D,N)` fibre attached to a cover index. -/
noncomputable def unbalancedShiftedSquareDyadicCoverCell
    (theta : ℝ) (Y R : ℕ) (i : ℤ × ℕ × ℕ × ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  admissibleUnbalancedShiftedSquareFibre theta Y R
    i.1 i.2.1 i.2.2.1 i.2.2.2

/-- The finite union of all fixed fibres in the dyadic cover. -/
noncomputable def unbalancedShiftedSquareDyadicCoverUnion
    (theta : ℝ) (Y R : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (unbalancedShiftedSquareDyadicCoverIndices theta Y R).biUnion
    (unbalancedShiftedSquareDyadicCoverCell theta Y R)

/-- Every admissible unbalanced tuple lies in the finite fixed-fibre union.
The `d` and `e*v` block boundaries are the exact half-open binary
boundaries selected by their floor logarithms. -/
theorem admissibleUnbalancedDyadicFactorTuples_subset_shiftedSquareDyadicCoverUnion
    (theta : ℝ) (Y R : ℕ) :
    admissibleUnbalancedDyadicFactorTuples theta Y R ⊆
      unbalancedShiftedSquareDyadicCoverUnion theta Y R := by
  classical
  rintro ⟨d, e, u, v⟩ hp
  obtain ⟨hcond, hvR, hshift⟩ :=
    mem_admissibleUnbalancedDyadicFactorTuples.mp hp
  obtain ⟨h, hh, hdiff, hadmissible⟩ := hshift
  have hcondFull := hcond
  obtain ⟨hd, he, _hu, hv, hdH, heH, _rest⟩ := hcond
  have hvone : 1 ≤ v := hv
  have hn : 0 < e * v := Nat.mul_pos he hv
  have hnH : e * v ≤ dyadicFactorHeight theta Y * R :=
    Nat.mul_le_mul heH (Nat.le_of_lt hvR)
  let D : ℕ := 2 ^ Nat.log 2 d
  let N : ℕ := 2 ^ Nat.log 2 (e * v)
  have hDmem : D ∈ dyadicLowerEndpoints (dyadicFactorHeight theta Y) := by
    exact pow_log_mem_dyadicLowerEndpoints hd hdH
  have hNmem : N ∈ dyadicLowerEndpoints (dyadicFactorHeight theta Y * R) := by
    exact pow_log_mem_dyadicLowerEndpoints hn hnH
  have hdblock : D ≤ d ∧ d < 2 * D := by
    simpa only [D, dyadicInterval, Finset.mem_Ico, pow_succ, Nat.mul_comm] using
      (mem_dyadicInterval_log hd)
  have hnblock : N ≤ e * v ∧ e * v < 2 * N := by
    simpa only [N, dyadicInterval, Finset.mem_Ico, pow_succ, Nat.mul_comm] using
      (mem_dyadicInterval_log hn)
  apply Finset.mem_biUnion.mpr
  refine ⟨(h, v, D, N), ?_, ?_⟩
  · exact mem_unbalancedShiftedSquareDyadicCoverIndices.mpr
      ⟨hh, hvone, hvR, hDmem, hNmem⟩
  · apply mem_admissibleUnbalancedShiftedSquareFibre.mpr
    exact ⟨hcondFull, hvR, ⟨h, hh, hdiff, hadmissible⟩, rfl,
      hdiff, hdblock.1, hdblock.2, hnblock.1, hnblock.2⟩

/-- The admissible unbalanced range is empty at `R = 0` and `R = 1` (and,
more generally, whenever `R ≤ 1`). -/
theorem admissibleUnbalancedDyadicFactorTuples_eq_empty_of_R_le_one
    (theta : ℝ) (Y R : ℕ) (hR : R ≤ 1) :
    admissibleUnbalancedDyadicFactorTuples theta Y R = ∅ := by
  classical
  ext p
  simp
  rcases p with ⟨d, e, u, v⟩
  intro hp
  have hmem := mem_admissibleUnbalancedDyadicFactorTuples.mp hp
  have hv : 0 < v := hmem.1.2.2.2.1
  have hvR : v < R := hmem.2.1
  omega

/-- Exact finite cardinality reduction from the complete admissible
unbalanced range to the sum of squarefree shifted-square blocks over the
displayed fixed `(h,v,D,N)` family. -/
theorem card_admissibleUnbalancedDyadicFactorTuples_le_sum_squarefreeShiftedSquareBlocks
    (theta : ℝ) (Y R : ℕ) :
    (admissibleUnbalancedDyadicFactorTuples theta Y R).card ≤
      ∑ i ∈ unbalancedShiftedSquareDyadicCoverIndices theta Y R,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card := by
  classical
  calc
    (admissibleUnbalancedDyadicFactorTuples theta Y R).card ≤
        (unbalancedShiftedSquareDyadicCoverUnion theta Y R).card :=
      Finset.card_le_card
        (admissibleUnbalancedDyadicFactorTuples_subset_shiftedSquareDyadicCoverUnion
          theta Y R)
    _ ≤ ∑ i ∈ unbalancedShiftedSquareDyadicCoverIndices theta Y R,
          (unbalancedShiftedSquareDyadicCoverCell theta Y R i).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ i ∈ unbalancedShiftedSquareDyadicCoverIndices theta Y R,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact card_admissibleUnbalancedShiftedSquareFibre_le_squarefreeBlock

end

end PellPaper
