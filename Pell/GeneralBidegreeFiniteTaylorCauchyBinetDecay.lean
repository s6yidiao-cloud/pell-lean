import Pell.GeneralBidegreeTaylorFactorialDecay
import Pell.FiniteWeightedCauchyBinetDecay

/-!
# Finite Cauchy--Binet decay for the sheared Taylor matrix

This module specializes the generic finite weighted Cauchy--Binet estimate to
the literal sheared Taylor factorization.  It retains the factorials in the
Taylor coefficients and leaves the coefficient-minor bound and its weighted
lower bound as explicit hypotheses.

It is deliberately finite: establishing a uniform bound for the residual
support sum and passing from finite truncations to the source exponential
matrix remain separate analytic steps.
-/

namespace PellPaper

open scoped BigOperators

/-- Rewrite one factorial-preserving Taylor scale as inverse factorials
times its exponential logarithmic weight. -/
theorem generalBidegreeTaylor_factorialScale_eq_invFactorials_mul_exp_neg_realWeight
    (m : generalBidegreeCoefficientMonomialIndex) (ellM ellX : ℝ) :
    ((Real.exp (-ellM)) ^ (m 0) * (Real.exp (-ellX)) ^ (m 1)) /
        (Nat.factorial (m 0) : ℝ) / (Nat.factorial (m 1) : ℝ) =
      (Nat.factorial (m 0) : ℝ)⁻¹ * (Nat.factorial (m 1) : ℝ)⁻¹ *
        Real.exp (-generalBidegreeRealWeight ellM ellX m) := by
  calc
    ((Real.exp (-ellM)) ^ (m 0) * (Real.exp (-ellX)) ^ (m 1)) /
        (Nat.factorial (m 0) : ℝ) / (Nat.factorial (m 1) : ℝ) =
        ((Real.exp (-ellM)) ^ (m 0) * (Real.exp (-ellX)) ^ (m 1)) *
          ((Nat.factorial (m 0) : ℝ)⁻¹ * (Nat.factorial (m 1) : ℝ)⁻¹) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
    _ = Real.exp (-generalBidegreeRealWeight ellM ellX m) *
          ((Nat.factorial (m 0) : ℝ)⁻¹ * (Nat.factorial (m 1) : ℝ)⁻¹) := by
            rw [← Real.exp_nat_mul (-ellM) (m 0),
              ← Real.exp_nat_mul (-ellX) (m 1), ← Real.exp_add]
            congr 1
            simp only [generalBidegreeRealWeight]
            ring
    _ = (Nat.factorial (m 0) : ℝ)⁻¹ * (Nat.factorial (m 1) : ℝ)⁻¹ *
        Real.exp (-generalBidegreeRealWeight ellM ellX m) := by
          ring

/-- A literal Taylor coefficient is bounded by its inverse factorials and
exponential logarithmic weight. -/
theorem abs_generalBidegreeTaylorCoefficient_le_invFactorials_mul_exp_neg_realWeight
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (ellM ellX : ℝ)
    (hα : |α r| ≤ Real.exp (-ellM))
    (hβ : |β r| ≤ Real.exp (-ellX)) :
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
      ((Nat.factorial (m 0) : ℝ)⁻¹ * (Nat.factorial (m 1) : ℝ)⁻¹) *
        Real.exp (-generalBidegreeRealWeight ellM ellX m) := by
  calc
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
        ((Real.exp (-ellM)) ^ (m 0) * (Real.exp (-ellX)) ^ (m 1)) /
          (Nat.factorial (m 0) : ℝ) / (Nat.factorial (m 1) : ℝ) :=
      abs_generalBidegreeTaylorCoefficient_le_exp_neg_realWeight_div_factorials
        A B α β m r ellM ellX hα hβ
    _ = _ :=
      generalBidegreeTaylor_factorialScale_eq_invFactorials_mul_exp_neg_realWeight
        m ellM ellX

/-- A finite sheared Taylor determinant bound obtained from columnwise
coefficient-evaluation bounds and a lower bound for the total logarithmic
weight of every nonzero selected coefficient minor.  The residual finite sum
retains the two inverse factorials attached to each Taylor exponent. -/
theorem abs_det_generalBidegreeFiniteTaylorEvaluationMatrix_le_factorial_mul_exp_neg_minWeight_mul_sum_invFactorials_pow
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (C : κ → ℝ) (ellM ellX W : ℝ)
    (hC_nonneg : ∀ q, 0 ≤ C q)
    (hU : ∀ r q,
      |generalBidegreeRectangularCoefficientMatrixReal A B s r q| ≤ C q)
    (hweight : ∀ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
      ((generalBidegreeRectangularCoefficientMatrixReal A B s).submatrix id p.1).det ≠ 0 →
        W ≤ ∑ i, generalBidegreeRealWeight ellM ellX (s (p.1 i)))
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeFiniteTaylorEvaluationMatrix A B α β s).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-W) *
          (∑ q, C q *
            ((Nat.factorial (s q 0) : ℝ)⁻¹ *
              (Nat.factorial (s q 1) : ℝ)⁻¹)) ^
            Fintype.card (generalBidegreeGrid A B) := by
  rw [generalBidegreeFiniteTaylorEvaluationMatrix_eq_transpose_mul,
    Matrix.det_transpose]
  apply abs_det_mul_le_factorial_mul_exp_neg_minWeight_mul_sum_pow
    (generalBidegreeRectangularCoefficientMatrixReal A B s)
    (generalBidegreeFiniteTaylorCoefficientMatrix A B α β s)
    C
    (fun q => (Nat.factorial (s q 0) : ℝ)⁻¹ *
      (Nat.factorial (s q 1) : ℝ)⁻¹)
    (fun q => generalBidegreeRealWeight ellM ellX (s q)) W
  · exact hC_nonneg
  · intro q
    exact mul_nonneg (by positivity) (by positivity)
  · exact hU
  · intro q r
    exact abs_generalBidegreeTaylorCoefficient_le_invFactorials_mul_exp_neg_realWeight
      A B α β (s q) r ellM ellX (hα r) (hβ r)
  · exact hweight

end PellPaper
