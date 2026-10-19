import Pell.GeneralBidegreeRectangularSharpTaylorDecay
import Pell.ShearedIntegralMinorTransport
import Pell.ShearedCubicDominance

/-!
# Strictness package for sheared determinant decay

This file separates the analytic comparison which turns the sharp exponential
determinant estimate into a literal bound below one from the algebraic
source-to-integral transport.  The rate hypothesis is deliberately stated in
logarithmic form, so a later mesh/cubic normalization only has to prove a
single real inequality.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The explicit sharp-area deficit occurring in the rectangular sheared
Taylor determinant bound. -/
def shearedSharpAreaDeficit (A B : ℕ) (ellM ellX mesh : ℝ) (Q : ℕ) : ℝ :=
  (∑ n ∈ Finset.range Q,
    ((Fintype.card (generalBidegreeGrid A B) : ℝ) -
      generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh))) * mesh

/-- The coordinate tail appearing in the sharp determinant estimate. -/
def shearedSharpAreaTail (A B : ℕ) : ℝ :=
  ((A + 2 * B : ℕ) : ℝ) + (B : ℝ)

/-- A logarithmic rate inequality turns an exponential cost and factorial
tail determinant bound into a strict bound below one. -/
theorem abs_mul_lt_one_of_exp_cost_and_factorial_exp_decay
    {n : Type*} [Fintype n]
    (cost W tail z d : ℝ)
    (hcost : |z| ≤ Real.exp cost)
    (hdet : |d| ≤ (Nat.factorial (Fintype.card n) : ℝ) *
      Real.exp (-W) * (Real.exp tail) ^ Fintype.card n)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card n) : ℝ) +
      tail * (Fintype.card n : ℝ) < W) :
    |z * d| < 1 := by
  have hfac_pos : 0 < (Nat.factorial (Fintype.card n) : ℝ) := by
    positivity
  have hupper : |z * d| ≤ Real.exp cost *
      ((Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
        (Real.exp tail) ^ Fintype.card n) := by
    rw [abs_mul]
    exact mul_le_mul hcost hdet (abs_nonneg _) (Real.exp_pos _).le
  calc
    |z * d| ≤ Real.exp cost *
        ((Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
          (Real.exp tail) ^ Fintype.card n) := hupper
    _ = Real.exp (cost + Real.log (Nat.factorial (Fintype.card n) : ℝ) - W +
        tail * (Fintype.card n : ℝ)) := by
      calc
        Real.exp cost *
            ((Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
              (Real.exp tail) ^ Fintype.card n) =
            Real.exp cost *
              (Real.exp (Real.log (Nat.factorial (Fintype.card n) : ℝ)) *
                Real.exp (-W) * Real.exp ((Fintype.card n : ℝ) * tail)) := by
              rw [Real.exp_log hfac_pos, Real.exp_nat_mul]
        _ = Real.exp (cost + Real.log (Nat.factorial (Fintype.card n) : ℝ) - W +
            tail * (Fintype.card n : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

/-- A cubic rank-deficit lower bound and a quadratic logarithmic budget imply
the rate inequality used by the strict determinant comparison.  This is the
exact point at which the existing eventual cubic-dominance lemma enters the
source-oriented analytic pipeline. -/
theorem logarithmic_rate_lt_of_cubic_quadratic_budget
    {n : Type*} [Fintype n]
    (cost W tail c C degree Y : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hdegree : 0 < degree) (hY : 1 < Y)
    (hdominates : C * degree ^ 2 ≤ (c / 2) * degree ^ 3)
    (hbudget : cost + Real.log (Nat.factorial (Fintype.card n) : ℝ) +
      tail * (Fintype.card n : ℝ) ≤ C * degree ^ 2 * Real.log Y)
    (hcubic : c * degree ^ 3 * Real.log Y ≤ W) :
    cost + Real.log (Nat.factorial (Fintype.card n) : ℝ) +
      tail * (Fintype.card n : ℝ) < W := by
  have hdominance_log : C * degree ^ 2 * Real.log Y <
      c * degree ^ 3 * Real.log Y := by
    have hneg := sheared_cubic_quadratic_log_exponent_neg
      hc hC hdegree hY hdominates
    linarith
  exact hbudget.trans_lt (hdominance_log.trans_le hcubic)

/-- The sharp rectangular exponential determinant estimate is strictly below
one after any factor with exponential cost satisfying the displayed logarithmic
rate inequality.  This is the source-oriented analytic interface: no choice
of coordinates or integral matrix has yet been made. -/
theorem abs_reindexedShearedDeterminant_mul_lt_one_of_sharpArea_rate
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
      shearedSharpAreaTail A B * (Fintype.card (generalBidegreeGrid A B) : ℝ) <
        shearedSharpAreaDeficit A B ellM ellX mesh Q) :
    |z *
      (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
        (shearedExponentialEvaluationMatrix A B S T)).det| < 1 := by
  let d := (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
    (shearedExponentialEvaluationMatrix A B S T)).det
  have hdet : |d| ≤ (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
      Real.exp (-(shearedSharpAreaDeficit A B ellM ellX mesh Q)) *
        (Real.exp (shearedSharpAreaTail A B)) ^
          Fintype.card (generalBidegreeGrid A B) := by
    simpa only [d, shearedSharpAreaDeficit, shearedSharpAreaTail] using
      (abs_det_reindex_shearedExponentialEvaluationMatrix_le_sharpArea_exp_tail
        A B eRows S T ellM ellX mesh hellM_pos hell hmesh Q hα hβ)
  exact abs_mul_lt_one_of_exp_cost_and_factorial_exp_decay
    cost (shearedSharpAreaDeficit A B ellM ellX mesh Q) (shearedSharpAreaTail A B)
    z d hcost hdet hrate

/-- The preceding source-oriented strict determinant bound with its rate
hypothesis discharged by an explicit cubic rank-deficit lower bound and a
quadratic analytic budget. -/
theorem abs_reindexedShearedDeterminant_mul_lt_one_of_sharpArea_cubicQuadraticBudget
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (S T : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ r,
      |generalBidegreeReindexedLogS A B eRows S r| ≤ Real.exp (-ellM))
    (hβ : ∀ r,
      |generalBidegreeReindexedShearedLogT A B eRows S T r| ≤ Real.exp (-ellX))
    (cost z c C degree Y : ℝ)
    (hcost : |z| ≤ Real.exp cost)
    (hc : 0 < c) (hC : 0 ≤ C) (hdegree : 0 < degree) (hY : 1 < Y)
    (hdominates : C * degree ^ 2 ≤ (c / 2) * degree ^ 3)
    (hbudget : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedSharpAreaTail A B * (Fintype.card (generalBidegreeGrid A B) : ℝ) ≤
        C * degree ^ 2 * Real.log Y)
    (hcubic : c * degree ^ 3 * Real.log Y ≤
      shearedSharpAreaDeficit A B ellM ellX mesh Q) :
    |z *
      (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
        (shearedExponentialEvaluationMatrix A B S T)).det| < 1 := by
  apply abs_reindexedShearedDeterminant_mul_lt_one_of_sharpArea_rate
    A B eRows S T ellM ellX mesh hellM_pos hell hmesh Q hα hβ cost z hcost
  exact logarithmic_rate_lt_of_cubic_quadratic_budget
    cost (shearedSharpAreaDeficit A B ellM ellX mesh Q) (shearedSharpAreaTail A B)
    c C degree Y hc hC hdegree hY hdominates hbudget hcubic

/-- The sharp-area rate inequality directly kills the source-oriented
denominator-cleared integral minor.  The standard bidegree convention is
obtained from this result by the already-proved column reflection. -/
theorem sourceOrientedSelectedIntegralMinor_det_eq_zero_of_sharpArea_rate
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
      shearedSharpAreaTail A B * (Fintype.card (generalBidegreeGrid A B) : ℝ) <
        shearedSharpAreaDeficit A B ellM ellX mesh Q) :
    ((sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).submatrix r id).det =
      0 := by
  apply sourceOrientedSelectedIntegralMinor_det_eq_zero_of_reindexedSheared_abs_lt_one
    A B points eRows r hr s₀ S T hden hcoords hS hT
  exact abs_reindexedShearedDeterminant_mul_lt_one_of_sharpArea_rate
    A B eRows S T ellM ellX mesh hellM_pos hell hmesh Q hα hβ cost
    ((∏ i : generalBidegreeFormIndex A B,
      ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
      s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)) hcost hrate

/-- The source-coordinate denominator and centre cost, together with the
sharp-area rate inequality, force the corresponding standard integral minor
to vanish. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_sharpArea_rate
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
      shearedSharpAreaTail A B * (Fintype.card (generalBidegreeGrid A B) : ℝ) <
        shearedSharpAreaDeficit A B ellM ellX mesh Q) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_sourceOriented A B points r
  exact sourceOrientedSelectedIntegralMinor_det_eq_zero_of_sharpArea_rate
    A B points eRows r hr s₀ S T hden hcoords hS hT ellM ellX mesh
    hellM_pos hell hmesh Q hα hβ cost hcost hrate

/-- A cubic lower bound for the sharp-area deficit may be supplied separately.
It is enough to prove the logarithmic budget below that cubic quantity. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_sharpArea_cubic_rate
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
    (hcubic : cubicGain ≤ shearedSharpAreaDeficit A B ellM ellX mesh Q)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedSharpAreaTail A B * (Fintype.card (generalBidegreeGrid A B) : ℝ) < cubicGain) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_sharpArea_rate
    A B points eRows r hr s₀ S T hden hcoords hS hT ellM ellX mesh
    hellM_pos hell hmesh Q hα hβ cost hcost
  exact hrate.trans_le hcubic

end

end PellPaper
