import Pell.BinaryHomogeneousCommonFactor
import Pell.BinaryHomogeneousFactorHeight

/-!
# Heights for the extracted integral common factor and residual components

The quotient bound includes zero dividends, using a nonzero complementary
factor. Exact gcd extraction then gives simultaneous coefficient bounds
without a supplied factorization, primitivity or height premise for factors.
-/

namespace PellPaper
noncomputable section

/-- A homogeneous quotient by a nonzero integral factor obeys the usual
binary factor-height bound, also when the dividend and quotient are zero. -/
theorem abs_coeff_homogeneous_binary_quotient_le
    (K D J : MvPolynomial (Fin 2) ℤ) (n j : ℕ) (H : ℝ)
    (hK : K.IsHomogeneous n) (hJ : J.IsHomogeneous j)
    (hD : D ≠ 0) (hfactor : K = D * J) (hH : 0 ≤ H)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H) (e : Fin 2 →₀ ℕ) :
    |((J.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H := by
  by_cases hK₀ : K = 0
  · have hJ₀ : J = 0 := (mul_eq_zero.mp (hfactor.symm.trans hK₀)).resolve_left hD
    simp only [hJ₀, MvPolynomial.coeff_zero, Int.cast_zero, abs_zero]
    positivity
  · exact abs_coeff_homogeneous_binary_factor_le K J n j H hK hJ hK₀
      ⟨D, by rw [hfactor, mul_comm]⟩ hH hcoeff e

/-- Exact common-target extraction with simultaneous heights. Every output
coefficient is bounded by `2^n*(n+1)*H`; common content and projective padding
are included in the integral factor. The residual affine pair is relatively
prime with maximum affine degree exactly its homogeneous degree. -/
theorem exists_bounded_homogeneous_binary_common_factor
    (A₀ B₀ : MvPolynomial (Fin 2) ℤ) (n : ℕ) (H : ℝ)
    (hA₀ : A₀.IsHomogeneous n) (hB₀ : B₀.IsHomogeneous n)
    (h₀ : A₀ ≠ 0 ∨ B₀ ≠ 0) (hH : 0 ≤ H)
    (hcoeffA : ∀ e, |((A₀.coeff e : ℤ) : ℝ)| ≤ H)
    (hcoeffB : ∀ e, |((B₀.coeff e : ℤ) : ℝ)| ≤ H) :
    ∃ (D A B : MvPolynomial (Fin 2) ℤ) (d b : ℕ),
      D ≠ 0 ∧ (A ≠ 0 ∨ B ≠ 0) ∧
      D.IsHomogeneous d ∧ A.IsHomogeneous b ∧ B.IsHomogeneous b ∧
      d + b = n ∧ A₀ = D * A ∧ B₀ = D * B ∧
      IsRelPrime (binaryDehomogenizeAtOne A) (binaryDehomogenizeAtOne B) ∧
      b = max (binaryDehomogenizeAtOne A).natDegree
        (binaryDehomogenizeAtOne B).natDegree ∧
      (∀ e, |((D.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
      (∀ e, |((A.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
      (∀ e, |((B.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) := by
  obtain ⟨D, A, B, d, b, hD₀, hAB₀, hD, hA, hB, hdb, hFA, hFB, hrel, hmax⟩ :=
    exists_homogeneous_binary_common_factor A₀ B₀ n hA₀ hB₀ h₀
  refine ⟨D, A, B, d, b, hD₀, hAB₀, hD, hA, hB, hdb, hFA, hFB, hrel, hmax, ?_,
    abs_coeff_homogeneous_binary_quotient_le A₀ D A n b H hA₀ hA hD₀ hFA hH hcoeffA,
    abs_coeff_homogeneous_binary_quotient_le B₀ D B n b H hB₀ hB hD₀ hFB hH hcoeffB⟩
  intro e
  rcases h₀ with hA₀₀ | hB₀₀
  · exact abs_coeff_homogeneous_binary_factor_le A₀ D n d H hA₀ hD hA₀₀
      ⟨A, hFA⟩ hH hcoeffA e
  · exact abs_coeff_homogeneous_binary_factor_le B₀ D n d H hB₀ hD hB₀₀
      ⟨B, hFB⟩ hH hcoeffB e

end
end PellPaper
