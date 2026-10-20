import Pell.BinaryHomogeneousValueHeight

/-!
# Integral coefficient heights for binary products

Expanding the first factor over its actual support gives one possible
coefficient of the second factor for each supported monomial. For a
homogeneous binary first factor, the proved support bound supplies the
degree-plus-one constant. These bounds include zero polynomials and degree
zero, and do not impose homogeneity on the second factor.

This is the coefficient-convolution step in the six-term eliminant
substitution of the manuscript and 832.
-/

namespace PellPaper

/-- Bound each actual product coefficient using the support of the first
factor. Both coefficient bounds are integral and may be zero. -/
theorem abs_coeff_mul_le_support_card_mul
    {σ : Type*} (P Q : MvPolynomial σ ℤ) (HP HQ : ℤ)
    (hHP : 0 ≤ HP) (hHQ : 0 ≤ HQ)
    (hP : ∀ e, |P.coeff e| ≤ HP) (hQ : ∀ e, |Q.coeff e| ≤ HQ)
    (e : σ →₀ ℕ) :
    |(P * Q).coeff e| ≤ (P.support.card : ℤ) * HP * HQ := by
  classical
  have hexpand : (P * Q).coeff e =
      ∑ s ∈ P.support, (MvPolynomial.monomial s (P.coeff s) * Q).coeff e := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_mul, MvPolynomial.coeff_sum]
  rw [hexpand]
  calc
    |∑ s ∈ P.support, (MvPolynomial.monomial s (P.coeff s) * Q).coeff e| ≤
        ∑ s ∈ P.support, |(MvPolynomial.monomial s (P.coeff s) * Q).coeff e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ P.support, HP * HQ := by
      apply Finset.sum_le_sum
      intro s _
      rw [MvPolynomial.coeff_monomial_mul']
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul (hP s) (hQ (e - s)) (abs_nonneg _) hHP
      · simpa using mul_nonneg hHP hHQ
    _ = (P.support.card : ℤ) * HP * HQ := by simp [mul_assoc]

/-- A homogeneous binary first factor of degree b has at most b+1
supported monomials. The second factor need not be homogeneous. -/
theorem abs_coeff_mul_homogeneous_binary_le
    (P Q : MvPolynomial (Fin 2) ℤ) (b : ℕ) (HP HQ : ℤ)
    (hhom : P.IsHomogeneous b) (hHP : 0 ≤ HP) (hHQ : 0 ≤ HQ)
    (hP : ∀ e, |P.coeff e| ≤ HP) (hQ : ∀ e, |Q.coeff e| ≤ HQ)
    (e : Fin 2 →₀ ℕ) :
    |(P * Q).coeff e| ≤ ((b : ℤ) + 1) * HP * HQ := by
  have hcard : (P.support.card : ℤ) ≤ (b : ℤ) + 1 := by
    exact_mod_cast card_support_homogeneous_binary_le P b hhom
  exact (abs_coeff_mul_le_support_card_mul P Q HP HQ hHP hHQ hP hQ e).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hHP) hHQ)

/-- Multiplication by one variable preserves a coefficient-height bound.
If the requested exponent has zero in that coordinate, the coefficient
is zero; subtraction is used only in the supported-coordinate branch. -/
theorem abs_coeff_mul_X_le
    {σ : Type*} (P : MvPolynomial σ ℤ) (HP : ℤ) (hHP : 0 ≤ HP)
    (hP : ∀ e, |P.coeff e| ≤ HP) (i : σ) (e : σ →₀ ℕ) :
    |(P * MvPolynomial.X i).coeff e| ≤ HP := by
  classical
  rw [MvPolynomial.coeff_mul_X']
  split_ifs
  · exact hP _
  · simpa using hHP

end PellPaper
