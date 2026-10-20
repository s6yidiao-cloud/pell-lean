import Pell.SourceNormalizedActualRankCubic
import Pell.ShearedActualRankDeterminantStrictness

/-!
# Source-normalized determinant strictness

This module is the literal endpoint of the source-normalized rank calculation.
It packages the rounded two-regime cubic gain and feeds it into the existing
integral-minor strictness theorem.  The remaining hypotheses are deliberately
the source's local coordinate, denominator-cost, and strict rate inputs; this
does not assert the auxiliary-curve or point-counting steps.
-/

namespace PellPaper

open scoped BigOperators Interval

noncomputable section

/-- The number of full high-branch source-normalized mesh cells retained by
the rounded two-regime rank calculation. -/
def sourceNormalizedHighMeshFloorCount (A B : ℕ) (m x : ℝ) : ℕ :=
  ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊

/-- The total number of retained source-normalized mesh cells. -/
def sourceNormalizedFloorMeshCount (A B : ℕ) (m x : ℝ) : ℕ :=
  A + sourceNormalizedHighMeshFloorCount A B m x

/-- The explicit determinant-side cubic gain from the rounded source mesh.
The final partial high cell is accounted for by the third mesh-cell loss. -/
def sourceNormalizedFloorCubicGain (A B : ℕ) (m x L : ℝ) : ℝ :=
  (B : ℝ) * L *
    ((B : ℝ) ^ 2 *
        (((A : ℝ) / (B : ℝ)) * m / 2 +
          x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
          x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
          3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
      (x / (B : ℝ)) *
        ((∑ n ∈ Finset.range A,
            sourceNormalizedTriangularCapError B m x
              (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
          ∑ n ∈ Finset.range
              ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊,
            sourceNormalizedShellCapError B m x
              (x * ((A : ℝ) / (B : ℝ)) +
                ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))))

/-- The rounded source-normalized cubic is a lower bound for the literal
rank-deficit exponent used by the determinant estimate. -/
theorem sourceNormalizedFloorCubicGain_le_actualRankDeficits
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m) :
    sourceNormalizedFloorCubicGain A B m x L ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
        (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
        (sourceNormalizedFloorMeshCount A B m x) := by
  simpa only [sourceNormalizedFloorCubicGain, sourceNormalizedFloorMeshCount,
    sourceNormalizedHighMeshFloorCount] using
    sourceNormalized_actualRadiusRankDeficits_ge_rescaledCubic_sub_three_mesh_floor
      A B m x L hB hm hmx hL hshear

/-- A strict source-normalized rounded-mesh rate budget makes the standard
cleared bidegree minor vanish.  This is the direct bridge from the checked
rank calculation to the determinant-method auxiliary relation. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_sourceNormalizedFloorCubic_rate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS A B eRows S row| ≤ Real.exp (-(m * L)))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows S T row| ≤ Real.exp (-(x * L)))
    (cost : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m x L) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_cubic_rate
    A B points eRows r hr s₀ S T hden hcoords hS hT
      (m * L) (x * L) (x * L)
      (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
      (mul_pos (lt_of_lt_of_le hm hmx) hL)
      (sourceNormalizedFloorMeshCount A B m x) hα hβ cost
      (sourceNormalizedFloorCubicGain A B m x L) hcost
  · exact sourceNormalizedFloorCubicGain_le_actualRankDeficits
      A B m x L hB hm hmx hL hshear
  · exact hrate

/-- The rounded source cubic with its finite cap-error sums replaced by the
checked polynomial boundary budget.  Keeping the exact floor count makes this
the form suited to an eventual explicit source rate calculation. -/
def sourceNormalizedFloorPolynomialCubicGain (A B : ℕ) (m x L : ℝ) : ℝ :=
  (B : ℝ) * L *
    ((B : ℝ) ^ 2 *
        (((A : ℝ) / (B : ℝ)) * m / 2 +
          x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
          x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
          3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
      (x / (B : ℝ)) *
        ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
          (sourceNormalizedHighMeshFloorCount A B m x : ℝ) *
            (((A : ℝ) + (sourceNormalizedHighMeshFloorCount A B m x : ℝ)) *
              (3 * x / (2 * m) + 1) + 1)))

/-- The polynomial-error rounded source cubic remains a lower bound for the
literal rank-deficit exponent. -/
theorem sourceNormalizedFloorPolynomialCubicGain_le_actualRankDeficits
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m) :
    sourceNormalizedFloorPolynomialCubicGain A B m x L ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
        (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
        (sourceNormalizedFloorMeshCount A B m x) := by
  simpa only [sourceNormalizedFloorPolynomialCubicGain,
    sourceNormalizedFloorMeshCount, sourceNormalizedHighMeshFloorCount] using
    sourceNormalized_actualRadiusRankDeficits_ge_rescaledCubic_sub_three_mesh_floor_polynomial
      A B m x L hB hm hmx hL hshear

/-- The polynomial-error source rate budget also gives standard cleared-minor
vanishing.  It is a convenience endpoint only: the local coordinate and
denominator estimates remain explicit inputs. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_sourceNormalizedFloorPolynomialCubic_rate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS A B eRows S row| ≤ Real.exp (-(m * L)))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows S T row| ≤ Real.exp (-(x * L)))
    (cost : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorPolynomialCubicGain A B m x L) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_cubic_rate
    A B points eRows r hr s₀ S T hden hcoords hS hT
      (m * L) (x * L) (x * L)
      (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
      (mul_pos (lt_of_lt_of_le hm hmx) hL)
      (sourceNormalizedFloorMeshCount A B m x) hα hβ cost
      (sourceNormalizedFloorPolynomialCubicGain A B m x L) hcost
  · exact sourceNormalizedFloorPolynomialCubicGain_le_actualRankDeficits
      A B m x L hB hm hmx hL hshear
  · exact hrate

end

end PellPaper
