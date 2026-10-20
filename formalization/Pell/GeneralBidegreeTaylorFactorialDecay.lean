import Pell.GeneralBidegreeTaylorCoefficientBounds

/-!
# Factorial-preserving Taylor decay on the sheared grid

The ordered Cauchy--Binet bound for `L:sheared` needs more than the bare
exponential weight of a Taylor coefficient: the two factorial denominators
are what make the sum over arbitrarily large Taylor supports uniformly
summable.  This module records that sharper finite estimate and packages its
row-weighted determinant consequence.  It deliberately does not assert an
infinite-series bound or any determinant tail estimate.
-/

namespace PellPaper

open scoped BigOperators

/-- A Taylor coefficient is bounded by its exponential logarithmic weight
while retaining both factorial denominators. -/
theorem abs_generalBidegreeTaylorCoefficient_le_exp_neg_realWeight_div_factorials
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (ellM ellX : ℝ)
    (hα : |α r| ≤ Real.exp (-ellM))
    (hβ : |β r| ≤ Real.exp (-ellX)) :
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
      ((Real.exp (-ellM)) ^ (m 0) * (Real.exp (-ellX)) ^ (m 1)) /
        (Nat.factorial (m 0) : ℝ) / (Nat.factorial (m 1) : ℝ) := by
  have hfac0pos : 0 < (Nat.factorial (m 0) : ℝ) := by positivity
  have hfac1pos : 0 < (Nat.factorial (m 1) : ℝ) := by positivity
  have hpowα : |α r| ^ (m 0) ≤ (Real.exp (-ellM)) ^ (m 0) :=
    pow_le_pow_left₀ (abs_nonneg _) hα _
  have hpowβ : |β r| ^ (m 1) ≤ (Real.exp (-ellX)) ^ (m 1) :=
    pow_le_pow_left₀ (abs_nonneg _) hβ _
  rw [generalBidegreeTaylorCoefficient, abs_div, abs_div, abs_mul,
    abs_pow, abs_pow, abs_of_pos hfac0pos, abs_of_pos hfac1pos]
  apply div_le_div_of_nonneg_right
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hpowα hpowβ
        (pow_nonneg (abs_nonneg _) _) (by positivity)
    · exact hfac0pos.le
  · exact hfac1pos.le

/-- The product of factorial-preserving Taylor scales splits into the
negative total logarithmic weight and the residual inverse-factorial product.
This is the exact finite form needed before summing Cauchy--Binet supports. -/
theorem prod_exp_neg_pows_div_factorials_eq_exp_neg_sum_mul_prod_inv_factorials
    {ι : Type*} [Fintype ι]
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (ellM ellX : ℝ) :
    (∏ q, ((Real.exp (-ellM)) ^ (s q 0) * (Real.exp (-ellX)) ^ (s q 1)) /
        (Nat.factorial (s q 0) : ℝ) / (Nat.factorial (s q 1) : ℝ)) =
      Real.exp (- ∑ q, generalBidegreeRealWeight ellM ellX (s q)) *
        ∏ q, (Nat.factorial (s q 0) : ℝ)⁻¹ *
          (Nat.factorial (s q 1) : ℝ)⁻¹ := by
  calc
    (∏ q, ((Real.exp (-ellM)) ^ (s q 0) * (Real.exp (-ellX)) ^ (s q 1)) /
        (Nat.factorial (s q 0) : ℝ) / (Nat.factorial (s q 1) : ℝ)) =
      ∏ q, ((Real.exp (-ellM)) ^ (s q 0) * (Real.exp (-ellX)) ^ (s q 1)) *
        ((Nat.factorial (s q 0) : ℝ)⁻¹ * (Nat.factorial (s q 1) : ℝ)⁻¹) := by
          apply Finset.prod_congr rfl
          intro q _
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    _ = (∏ q, (Real.exp (-ellM)) ^ (s q 0) * (Real.exp (-ellX)) ^ (s q 1)) *
        ∏ q, (Nat.factorial (s q 0) : ℝ)⁻¹ *
          (Nat.factorial (s q 1) : ℝ)⁻¹ := by
          rw [Finset.prod_mul_distrib]
    _ = _ := by
      rw [prod_exp_neg_pows_eq_exp_neg_sum_generalBidegreeRealWeight]

/-- A square finite Taylor coefficient determinant retains both the
exponential total-weight decay and the inverse factorials of every selected
exponent row. -/
theorem abs_det_generalBidegreeFiniteTaylorCoefficientMatrix_le_factorial_mul_exp_neg_totalWeight_mul_prod_inv_factorials
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (ellM ellX : ℝ)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeFiniteTaylorCoefficientMatrix A B α β s).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        (Real.exp (- ∑ q, generalBidegreeRealWeight ellM ellX (s q)) *
          ∏ q, (Nat.factorial (s q 0) : ℝ)⁻¹ *
            (Nat.factorial (s q 1) : ℝ)⁻¹) := by
  calc
    |(generalBidegreeFiniteTaylorCoefficientMatrix A B α β s).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        ∏ q, ((Real.exp (-ellM)) ^ (s q 0) * (Real.exp (-ellX)) ^ (s q 1)) /
          (Nat.factorial (s q 0) : ℝ) / (Nat.factorial (s q 1) : ℝ) := by
      apply abs_det_le_factorial_mul_prod_rowBounds
        (generalBidegreeFiniteTaylorCoefficientMatrix A B α β s)
        (fun q => ((Real.exp (-ellM)) ^ (s q 0) *
          (Real.exp (-ellX)) ^ (s q 1)) /
          (Nat.factorial (s q 0) : ℝ) / (Nat.factorial (s q 1) : ℝ))
      intro q r
      exact abs_generalBidegreeTaylorCoefficient_le_exp_neg_realWeight_div_factorials
        A B α β (s q) r ellM ellX (hα r) (hβ r)
    _ = _ := by
      rw [prod_exp_neg_pows_div_factorials_eq_exp_neg_sum_mul_prod_inv_factorials]

end PellPaper
