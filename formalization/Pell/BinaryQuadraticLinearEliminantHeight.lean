import Pell.BinaryQuadraticLinearEliminant
import Pell.BinaryHomogeneousProductHeight

/-!
# Coefficient height of the actual six-term eliminant

At a fixed coefficient, each product of degree-b input forms has at most
b+1 summands. Summing the six terms in the literal substitution gives
6*(b+1)*|c|*HF^2*HG. No nonvanishing or primitivity condition is needed.
-/

namespace PellPaper

noncomputable section
open scoped BigOperators

private theorem abs_sum_three_two_le (f : Fin 3 → Fin 2 → ℤ) (C : ℤ)
    (hf : ∀ i t, |f i t| ≤ C) : |∑ i : Fin 3, ∑ t : Fin 2, f i t| ≤ 6 * C := by
  calc
    |∑ i : Fin 3, ∑ t : Fin 2, f i t| ≤ ∑ i : Fin 3, ∑ t : Fin 2, |f i t| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _t : Fin 2, C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro t _
      exact hf i t
    _ = 6 * C := by simp; ring

private theorem substitution_product_coeff_le
    (A B : MvPolynomial (Fin 2) ℤ) (b : ℕ) (HF : ℤ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b) (hHF : 0 ≤ HF)
    (hcoeffA : ∀ e, |A.coeff e| ≤ HF) (hcoeffB : ∀ e, |B.coeff e| ≤ HF)
    (i : Fin 3) (e : Fin 2 →₀ ℕ) :
    |(B ^ (2 - i.val) * (-A) ^ i.val).coeff e| ≤ ((b : ℤ) + 1) * HF ^ 2 := by
  have hAA := abs_coeff_mul_homogeneous_binary_le A A b HF HF hA hHF hHF
    hcoeffA hcoeffA e
  have hBB := abs_coeff_mul_homogeneous_binary_le B B b HF HF hB hHF hHF
    hcoeffB hcoeffB e
  have hBnegA := abs_coeff_mul_homogeneous_binary_le B (-A) b HF HF hB hHF hHF
    hcoeffB (fun e => by simpa using hcoeffA e) e
  fin_cases i
  · simpa [pow_two, mul_assoc] using hBB
  · simpa [pow_two, mul_assoc] using hBnegA
  · simpa [pow_two, mul_assoc] using hAA

/-- Explicit coefficient height for the literal c*G(B,-A;y) polynomial.
The bound retains the six terms and only b+1 product summands, rather than
charging all (b+1)^2 coefficient pairs. Zero content, forms and heights
are permitted, and all input coefficient signs are unrestricted. -/
theorem abs_coeff_quadraticLinearEliminant_le
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ)
    (b : ℕ) (HF HG : ℤ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b)
    (hHF : 0 ≤ HF) (hHG : 0 ≤ HG)
    (hcoeffA : ∀ e, |A.coeff e| ≤ HF) (hcoeffB : ∀ e, |B.coeff e| ≤ HF)
    (hg : ∀ i t, |g i t| ≤ HG) (e : Fin 2 →₀ ℕ) :
    |(quadraticLinearEliminant g c A B).coeff e| ≤
      6 * ((b : ℤ) + 1) * |c| * HF ^ 2 * HG := by
  classical
  have hbase : 0 ≤ ((b : ℤ) + 1) * HF ^ 2 := by positivity
  have hterm (i : Fin 3) (t : Fin 2) :
      |(MvPolynomial.C (g i t) * B ^ (2 - i.val) * (-A) ^ i.val *
          MvPolynomial.X t).coeff e| ≤ HG * (((b : ℤ) + 1) * HF ^ 2) := by
    have hprod := substitution_product_coeff_le A B b HF hA hB hHF hcoeffA hcoeffB i
    have hvar := abs_coeff_mul_X_le (B ^ (2 - i.val) * (-A) ^ i.val)
      (((b : ℤ) + 1) * HF ^ 2) hbase hprod t e
    rw [mul_assoc (MvPolynomial.C (g i t)),
      mul_assoc (MvPolynomial.C (g i t)), MvPolynomial.coeff_C_mul, abs_mul]
    exact mul_le_mul (hg i t) hvar (abs_nonneg _) hHG
  have hsum :
      |(∑ i : Fin 3, ∑ t : Fin 2,
        MvPolynomial.C (g i t) * B ^ (2 - i.val) * (-A) ^ i.val *
          MvPolynomial.X t).coeff e| ≤ 6 * HG * (((b : ℤ) + 1) * HF ^ 2) := by
    rw [mul_assoc (6 : ℤ) HG]
    simp only [MvPolynomial.coeff_sum]
    exact abs_sum_three_two_le _ _ hterm
  rw [quadraticLinearEliminant, MvPolynomial.coeff_C_mul, abs_mul]
  calc
    _ ≤ |c| * (6 * HG * (((b : ℤ) + 1) * HF ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg c)
    _ = _ := by ring

end
end PellPaper
