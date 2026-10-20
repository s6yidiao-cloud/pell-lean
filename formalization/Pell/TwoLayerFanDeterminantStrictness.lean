import Pell.TwoLayerFanDeterminantDecay
import Pell.ShearedDeterminantStrictness

/-!
# Strict integral-minor vanishing in the exact two-layer fan

This module turns the exact two-layer determinant decay into a literal
strict bound below one after an arbitrary exponential clearing-cost factor.
It then feeds that bound through the existing source-oriented denominator
transport.  The only remaining numerical obligation is the displayed
logarithmic rate inequality; no mesh or area-envelope loss is introduced.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The coordinate Taylor tail in the exact `A = 1` two-layer determinant
estimate. -/
def twoLayerFanTaylorTail (B : ℕ) : ℝ :=
  ((1 + 2 * B : ℕ) : ℝ) + (B : ℝ)

/-- An exponential clearing-cost bound and the exact two-layer fan decay
give a strict product bound whenever their logarithmic rate is positive. -/
theorem abs_reindexedShearedDeterminant_mul_lt_one_of_twoLayerFan_rate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B k : ℕ) (eRows : ι ≃ generalBidegreeGrid 1 B)
    (S T : ι → ℝ) (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hα : ∀ r,
      |generalBidegreeReindexedLogS 1 B eRows S r| ≤ Real.exp (-ellM))
    (hβ : ∀ r,
      |generalBidegreeReindexedShearedLogT 1 B eRows S T r| ≤
        Real.exp (-ellX))
    (cost z : ℝ)
    (hcost : |z| ≤ Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    |z *
      (Matrix.reindex eRows (generalBidegreeGridPointEquiv 1 B)
        (shearedExponentialEvaluationMatrix 1 B S T)).det| < 1 := by
  apply abs_mul_lt_one_of_exp_cost_and_factorial_exp_decay
    (n := generalBidegreeGrid 1 B)
    cost (twoLayerWeight B k ellM ellX) (twoLayerFanTaylorTail B) z
    ((Matrix.reindex eRows (generalBidegreeGridPointEquiv 1 B)
      (shearedExponentialEvaluationMatrix 1 B S T)).det)
    hcost
  · simpa only [twoLayerFanTaylorTail] using
      abs_det_reindex_shearedExponentialEvaluationMatrix_le_twoLayerFan_exp_tail
        B k eRows S T ellM ellX hellM hkpos hkB hfanLower hfanUpper hα hβ
  · exact hrate

/-- The exact fan rate kills the source-oriented denominator-cleared
selected integral minor. -/
theorem sourceOrientedSelectedIntegralMinor_det_eq_zero_of_twoLayerFan_rate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B k : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (eRows : ι ≃ generalBidegreeGrid 1 B)
    (r : generalBidegreeFormIndex 1 B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv 1 B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS 1 B eRows S row| ≤ Real.exp (-ellM))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT 1 B eRows S T row| ≤
        Real.exp (-ellX))
    (cost : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex 1 B,
          ((points (r i)).1.2 : ℝ) ^ 1 * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((1 + 1) * (B + 1) * (1 + 2 * B)) / 2)| ≤
        Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    ((sourceOrientedGeneralBidegreeClearedEvaluationMatrix 1 B points).submatrix
      r id).det = 0 := by
  apply
    sourceOrientedSelectedIntegralMinor_det_eq_zero_of_reindexedSheared_abs_lt_one
      1 B points eRows r hr s₀ S T hden hcoords hS hT
  exact abs_reindexedShearedDeterminant_mul_lt_one_of_twoLayerFan_rate
    B k eRows S T ellM ellX hellM hkpos hkB hfanLower hfanUpper hα hβ
    cost
    ((∏ i : generalBidegreeFormIndex 1 B,
        ((points (r i)).1.2 : ℝ) ^ 1 * ((points (r i)).2.2 : ℝ) ^ B) *
      s₀ ^ (((1 + 1) * (B + 1) * (1 + 2 * B)) / 2))
    hcost hrate

/-- The exact fan rate kills the corresponding standard homogeneous
integral selected minor. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_twoLayerFan_rate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B k : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (eRows : ι ≃ generalBidegreeGrid 1 B)
    (r : generalBidegreeFormIndex 1 B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv 1 B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hα : ∀ row,
      |generalBidegreeReindexedLogS 1 B eRows S row| ≤ Real.exp (-ellM))
    (hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT 1 B eRows S T row| ≤
        Real.exp (-ellX))
    (cost : ℝ)
    (hcost :
      |(∏ i : generalBidegreeFormIndex 1 B,
          ((points (r i)).1.2 : ℝ) ^ 1 * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((1 + 1) * (B + 1) * (1 + 2 * B)) / 2)| ≤
        Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    ((generalBidegreeFormEvaluationMatrix 1 B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_sourceOriented 1 B points r
  exact sourceOrientedSelectedIntegralMinor_det_eq_zero_of_twoLayerFan_rate
    B k points eRows r hr s₀ S T hden hcoords hS hT ellM ellX hellM
    hkpos hkB hfanLower hfanUpper hα hβ cost hcost hrate

end

end PellPaper
