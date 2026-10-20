import Pell.BinaryProjectiveDerivativeResultant
import Pell.IntegralCofactorKernelBound
import Mathlib.Tactic

/-!
# A coefficient-height bound for the projective derivative resultant

For a homogeneous integral binary form of positive degree `j`, this file
bounds the fixed projective derivative resultant by applying the
factorial/Leibniz determinant estimate to its literal Sylvester matrix.

The bound is uniform in the form.  It uses only a common coefficient bound
`H`; squarefreeness and resultant nonvanishing are deliberately separate.
-/

namespace PellPaper

open Polynomial
open Finsupp

noncomputable section

private theorem binary_homogeneous_support_card_le
    (Q : MvPolynomial (Fin 2) ℤ) (n : ℕ)
    (hQ : Q.IsHomogeneous n) :
    Q.support.card ≤ n + 1 := by
  classical
  have hcard : Q.support.card ≤ (Finset.range (n + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun d : Fin 2 →₀ ℕ ↦ d 0)
    · intro d hd
      have hddegree := hQ (MvPolynomial.mem_support_iff.mp hd)
      have : d 0 + d 1 = n := by
        simpa [weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hddegree
      have hdlt : d 0 < n + 1 := by omega
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hdlt)
    · intro d hd e he hde
      change d 0 = e 0 at hde
      have hddegree := hQ (MvPolynomial.mem_support_iff.mp hd)
      have hedegree := hQ (MvPolynomial.mem_support_iff.mp he)
      have hd' : d 0 + d 1 = n := by
        simpa [weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hddegree
      have he' : e 0 + e 1 = n := by
        simpa [weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hedegree
      have hde_one : d 1 = e 1 := by omega
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact hde
      · exact hde_one
  simpa using hcard

private theorem abs_coeff_binaryDehomogenizeAtOne_le
    (Q : MvPolynomial (Fin 2) ℤ) (n : ℕ) {K : ℤ}
    (hQ : Q.IsHomogeneous n) (hK : 0 ≤ K)
    (hcoeff : ∀ d ∈ Q.support, |Q.coeff d| ≤ K) (k : ℕ) :
    |(binaryDehomogenizeAtOne Q).coeff k| ≤ (n + 1 : ℕ) * K := by
  classical
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_eq', Polynomial.finsetSum_coeff]
  calc
    |(∑ d ∈ Q.support,
        (Polynomial.C (Q.coeff d) *
          ∏ i, ![Polynomial.X, (1 : Polynomial ℤ)] i ^ d i).coeff k)| ≤
        ∑ d ∈ Q.support,
          |(Polynomial.C (Q.coeff d) *
            ∏ i, ![Polynomial.X, (1 : Polynomial ℤ)] i ^ d i).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Q.support, K := by
      gcongr with d hd
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_pow, mul_one, Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.coeff_monomial]
      split_ifs
      · simpa using hcoeff d hd
      · simp [hK]
    _ = (Q.support.card : ℤ) * K := by simp
    _ ≤ (n + 1 : ℕ) * K := by
      gcongr
      exact_mod_cast binary_homogeneous_support_card_le Q n hQ

private theorem abs_coeff_pderiv_le
    (J : MvPolynomial (Fin 2) ℤ) (j : ℕ) {H : ℤ}
    (hJ : J.IsHomogeneous j) (hj : 0 < j) (hH : 0 ≤ H)
    (hcoeff : ∀ d, |J.coeff d| ≤ H)
    (i : Fin 2) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (MvPolynomial.pderiv i J).support) :
    |(MvPolynomial.pderiv i J).coeff d| ≤ (j : ℤ) * H := by
  have hddegree := hJ.pderiv (MvPolynomial.mem_support_iff.mp hd)
  have hd' : d 0 + d 1 = j - 1 := by
    simpa [weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hddegree
  have hi : d i + 1 ≤ j := by
    fin_cases i
    · simpa using (show d 0 + 1 ≤ j by omega)
    · simpa using (show d 1 + 1 ≤ j by omega)
  rw [MvPolynomial.coeff_pderiv]
  calc
    |J.coeff (d + Finsupp.single i 1) * (d i + 1)| =
        |J.coeff (d + Finsupp.single i 1)| * (d i + 1 : ℤ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d i + 1 : ℤ))]
    _ ≤ H * (j : ℤ) := by
      gcongr
      · exact hcoeff _
      · exact_mod_cast hi
    _ = (j : ℤ) * H := by ring

private theorem abs_coeff_dehomogenized_pderiv_le
    (J : MvPolynomial (Fin 2) ℤ) (j : ℕ) {H : ℤ}
    (hJ : J.IsHomogeneous j) (hj : 0 < j) (hH : 0 ≤ H)
    (hcoeff : ∀ d, |J.coeff d| ≤ H)
    (i : Fin 2) (k : ℕ) :
    |(binaryDehomogenizeAtOne (MvPolynomial.pderiv i J)).coeff k| ≤
      (j : ℤ) ^ 2 * H := by
  have hbound := abs_coeff_binaryDehomogenizeAtOne_le
    (MvPolynomial.pderiv i J) (j - 1) (hJ.pderiv)
    (mul_nonneg (by positivity) hH)
    (fun d hd ↦ abs_coeff_pderiv_le J j hJ hj hH hcoeff i d hd) k
  rw [show j - 1 + 1 = j by omega] at hbound
  calc
    |(binaryDehomogenizeAtOne (MvPolynomial.pderiv i J)).coeff k| ≤
        (j : ℤ) * ((j : ℤ) * H) := hbound
    _ = (j : ℤ) ^ 2 * H := by ring

/-- The fixed projective derivative resultant has an explicit
factorial/Leibniz height bound in terms of the homogeneous degree and a
uniform integral coefficient bound. -/
theorem abs_binaryProjectiveDerivativeResultant_le_factorial_mul_pow
    (J : MvPolynomial (Fin 2) ℤ) (j : ℕ) {H : ℤ}
    (hJ : J.IsHomogeneous j) (hj : 0 < j)
    (hH : 0 ≤ H) (hcoeff : ∀ d, |J.coeff d| ≤ H) :
    |binaryProjectiveDerivativeResultant J j| ≤
      ((2 * (j - 1)).factorial : ℤ) *
        (((j : ℤ) ^ 2 * H) ^ (2 * (j - 1))) := by
  let A : Polynomial ℤ :=
    binaryDehomogenizeAtOne (MvPolynomial.pderiv 0 J)
  let B : Polynomial ℤ :=
    binaryDehomogenizeAtOne (MvPolynomial.pderiv 1 J)
  have hentry : ∀ r c,
      |Polynomial.sylvester A B (j - 1) (j - 1) r c| ≤
        (j : ℤ) ^ 2 * H := by
    intro r c
    induction c using Fin.addCases with
    | left c =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact abs_coeff_dehomogenized_pderiv_le J j hJ hj hH hcoeff 1 _
        · simpa using mul_nonneg (sq_nonneg (j : ℤ)) hH
    | right c =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact abs_coeff_dehomogenized_pderiv_le J j hJ hj hH hcoeff 0 _
        · simpa using mul_nonneg (sq_nonneg (j : ℤ)) hH
  have hdet := abs_det_le_factorial_mul_pow
    (Polynomial.sylvester A B (j - 1) (j - 1))
    (mul_nonneg (sq_nonneg (j : ℤ)) hH) hentry
  change |Polynomial.resultant A B (j - 1) (j - 1)| ≤ _
  change |(Polynomial.sylvester A B (j - 1) (j - 1)).det| ≤ _
  simpa [two_mul] using hdet

end
end PellPaper
