import Pell.GeneralBidegreeActualRankTaylorDecay
import Pell.ShearedDeterminantStrictness
import Pell.ShearedIntegralMinorTransport

/-!
# Strictness from literal positive-ball rank deficits

This module is the source-oriented endpoint for a shifted low/high rank-cap
calculation.  It deliberately uses the literal rank-deficit exponent from
`GeneralBidegreeActualRankTaylorDecay`, rather than the older continuous
sharp-area envelope.  Thus a cubic lower bound for the actual mesh deficit
can be fed directly into the integral-minor vanishing argument.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The coordinate tail in the actual-rank Taylor determinant estimate. -/
def shearedActualRankTaylorTail (A B : ℕ) : ℝ :=
  ((A + 2 * B : ℕ) : ℝ) + (B : ℝ)

/-- The source reindexed sheared determinant is strictly below one after an
exponential cost whenever the literal positive-ball rank deficit exceeds the
factorial and coordinate-tail logarithmic budget. -/
theorem abs_reindexedShearedDeterminant_mul_lt_one_of_actualPositiveBallRankDeficits_rate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (S T : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ r,
      |generalBidegreeReindexedLogS A B eRows S r| ≤ Real.exp (-ellM))
    (hβ : ∀ r,
      |generalBidegreeReindexedShearedLogT A B eRows S T r| ≤ Real.exp (-ellX))
    (cost z : ℝ)
    (hcost : |z| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      generalBidegreeScaledActualPositiveBallRankDeficits A B ellM ellX mesh
        hellM_pos hell Q) :
    |z *
      (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
        (shearedExponentialEvaluationMatrix A B S T)).det| < 1 := by
  let d := (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
    (shearedExponentialEvaluationMatrix A B S T)).det
  have hdet : |d| ≤ (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
      Real.exp (-(generalBidegreeScaledActualPositiveBallRankDeficits A B ellM ellX mesh
        hellM_pos hell Q)) *
        (Real.exp (shearedActualRankTaylorTail A B)) ^
          Fintype.card (generalBidegreeGrid A B) := by
    simpa only [d, generalBidegreeScaledActualPositiveBallRankDeficits,
      shearedActualRankTaylorTail] using
      (abs_det_reindex_shearedExponentialEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail
        A B eRows S T ellM ellX mesh hellM_pos hell hmesh Q hα hβ)
  exact abs_mul_lt_one_of_exp_cost_and_factorial_exp_decay
    cost (generalBidegreeScaledActualPositiveBallRankDeficits A B ellM ellX mesh
      hellM_pos hell Q) (shearedActualRankTaylorTail A B) z d hcost hdet hrate

/-- The preceding strict actual-rank determinant estimate kills the
source-oriented denominator-cleared integral minor. -/
theorem sourceOrientedSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_rate
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
    (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS A B eRows S row| ≤ Real.exp (-ellM))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows S T row| ≤ Real.exp (-ellX))
    (cost : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      generalBidegreeScaledActualPositiveBallRankDeficits A B ellM ellX mesh
        hellM_pos hell Q) :
    ((sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).submatrix r id).det =
      0 := by
  apply sourceOrientedSelectedIntegralMinor_det_eq_zero_of_reindexedSheared_abs_lt_one
    A B points eRows r hr s₀ S T hden hcoords hS hT
  exact abs_reindexedShearedDeterminant_mul_lt_one_of_actualPositiveBallRankDeficits_rate
    A B eRows S T ellM ellX mesh hellM_pos hell hmesh Q hα hβ cost
    ((∏ i : generalBidegreeFormIndex A B,
      ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
      s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)) hcost hrate

/-- A separately established cubic lower bound for the actual-rank mesh
deficit suffices for source-oriented integral-minor vanishing. -/
theorem sourceOrientedSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_cubic_rate
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
    (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS A B eRows S row| ≤ Real.exp (-ellM))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows S T row| ≤ Real.exp (-ellX))
    (cost cubicGain : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hcubic : cubicGain ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B ellM ellX mesh
        hellM_pos hell Q)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) < cubicGain) :
    ((sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).submatrix r id).det =
      0 := by
  apply sourceOrientedSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_rate
    A B points eRows r hr s₀ S T hden hcoords hS hT ellM ellX mesh
    hellM_pos hell hmesh Q hα hβ cost hcost
  exact hrate.trans_le hcubic

/-- The standard bidegree convention follows from the source-oriented
actual-rank cubic conclusion by the established column reflection. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_cubic_rate
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
    (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS A B eRows S row| ≤ Real.exp (-ellM))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows S T row| ≤ Real.exp (-ellX))
    (cost cubicGain : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hcubic : cubicGain ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B ellM ellX mesh
        hellM_pos hell Q)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) < cubicGain) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_sourceOriented A B points r
  exact sourceOrientedSelectedIntegralMinor_det_eq_zero_of_actualPositiveBallRankDeficits_cubic_rate
    A B points eRows r hr s₀ S T hden hcoords hS hT ellM ellX mesh
    hellM_pos hell hmesh Q hα hβ cost cubicGain hcost hcubic hrate

end

end PellPaper
