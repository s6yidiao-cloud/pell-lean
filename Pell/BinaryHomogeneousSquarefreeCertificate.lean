import Pell.BinaryHomogeneousSquarefreeDecomposition
import Pell.BinaryProjectiveDerivativeResultantAffine
import Pell.BinaryHomogeneousFactorHeight
import Pell.BinaryProjectiveDerivativeResultantLogHeight

/-!
# Actual squarefree-factor certificates and their heights

The square decomposition, affine resultant criterion, and proved factor
height construct a nonzero resultant certificate from the original
nonzero odd-degree binary form. The content height is obtained from actual
integer divisibility of a nonzero coefficient. No factorization or resultant
nonvanishing is supplied by the caller.
-/

namespace PellPaper

noncomputable section

/-- A constant integral divisor of a nonzero multivariate polynomial is
bounded by any absolute coefficient bound for that polynomial. -/
theorem abs_constant_divisor_le_of_coeff_bound
    {σ : Type*} (K : MvPolynomial σ ℤ) (c H : ℤ)
    (hK0 : K ≠ 0) (hcK : MvPolynomial.C c ∣ K)
    (hcoeff : ∀ e, |K.coeff e| ≤ H) : |c| ≤ H := by
  obtain ⟨e, he⟩ := MvPolynomial.exists_coeff_ne_zero hK0
  have hdiv : c ∣ K.coeff e := (MvPolynomial.C_dvd_iff_dvd_coeff c K).mp hcK e
  have hn := Int.natAbs_le_of_dvd_ne_zero hdiv he
  have hcast : (c.natAbs : ℤ) ≤ ((K.coeff e).natAbs : ℤ) := by exact_mod_cast hn
  have habs : |c| ≤ |K.coeff e| := by simpa only [Int.natCast_natAbs] using hcast
  exact habs.trans (hcoeff e)

/-- Construct the literal square-content factorization and the nonzero
certificate `2*c*Res(∂₀J,∂₁J)`, with an explicit logarithmic bound in terms
of the original coefficient height. This is uniform in the original form
and its degree; no hidden height or squarefree-factor inputs remain. -/
theorem exists_homogeneous_square_factor_with_bounded_resultant_certificate
    (K : MvPolynomial (Fin 2) ℤ) (d H : ℕ)
    (hK : K.IsHomogeneous d) (hK0 : K ≠ 0) (hd : Odd d) (hH : 0 < H)
    (hcoeff : ∀ e, |K.coeff e| ≤ (H : ℤ)) :
    ∃ (c : ℤ) (R J : MvPolynomial (Fin 2) ℤ) (m j : ℕ),
      K = MvPolynomial.C c * R ^ 2 * J ∧
      c ≠ 0 ∧ Squarefree c ∧ |c| ≤ (H : ℤ) ∧ R ≠ 0 ∧ J ≠ 0 ∧
      R.IsHomogeneous m ∧ J.IsHomogeneous j ∧
      d = 2 * m + j ∧ Odd j ∧ 0 < j ∧
      (∀ a : ℤ, (∀ e : Fin 2 →₀ ℕ, a ∣ J.coeff e) → IsUnit a) ∧
      (∀ e, |J.coeff e| ≤ ((2 ^ d * (d + 1) * H : ℕ) : ℤ)) ∧
      2 * c * binaryProjectiveDerivativeResultant J j ≠ 0 ∧
      Real.log ((2 * c * binaryProjectiveDerivativeResultant J j).natAbs : ℝ) ≤
        Real.log 2 + Real.log (H : ℝ) +
          Real.log ((2 * (j - 1)).factorial : ℝ) +
            (2 * (j - 1) : ℕ) *
              (2 * Real.log (j : ℝ) + (d : ℝ) * Real.log 2 +
                Real.log ((d : ℝ) + 1) + Real.log (H : ℝ)) := by
  obtain ⟨c, R, J, m, j, hfactor, hc, hcsq, hR0, hJ0, hJK, hR, hJ,
    hledger, hjodd, hj, hprim, _, _, hsqRat, hgap⟩ :=
    exists_homogeneous_content_square_primitive_affine_squarefree K d hK hK0 hd
  have hcK : MvPolynomial.C c ∣ K :=
    ⟨R ^ 2 * J, by rw [hfactor, mul_assoc]⟩
  have hcHeight : |c| ≤ (H : ℤ) :=
    abs_constant_divisor_le_of_coeff_bound K c H hK0 hcK hcoeff
  let HJ : ℕ := 2 ^ d * (d + 1) * H
  have hHJ : 0 < HJ := by dsimp [HJ]; positivity
  have hcoeffR : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ (H : ℝ) := by
    intro e
    exact_mod_cast hcoeff e
  have hJHeight : ∀ e, |J.coeff e| ≤ (HJ : ℤ) := by
    intro e
    have h := abs_coeff_homogeneous_binary_factor_le K J d j H
      hK hJ hK0 hJK (by positivity) hcoeffR e
    dsimp only [HJ]
    exact_mod_cast h
  have hres : binaryProjectiveDerivativeResultant J j ≠ 0 :=
    binaryProjectiveDerivativeResultant_ne_zero_of_affine_squarefree J j hJ hj hsqRat hgap
  have hcert : 2 * c * binaryProjectiveDerivativeResultant J j ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hc) hres
  have hcHeightR : (c.natAbs : ℝ) ≤ (H : ℝ) := by
    have h : (c.natAbs : ℤ) ≤ (H : ℤ) := by simpa only [Int.natCast_natAbs] using hcHeight
    exact_mod_cast h
  have hlogc : Real.log (c.natAbs : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr hc) hcHeightR
  have hlogHJ : Real.log (HJ : ℝ) =
      (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Real.log (H : ℝ) := by
    dsimp only [HJ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlog := log_natAbs_two_mul_content_mul_binaryProjectiveDerivativeResultant_le
    J j HJ c hJ hj hHJ hJHeight hc hres
  rw [hlogHJ] at hlog
  refine ⟨c, R, J, m, j, hfactor, hc, hcsq, hcHeight, hR0, hJ0,
    hR, hJ, hledger, hjodd, hj, hprim, hJHeight, hcert, ?_⟩
  linarith

end
end PellPaper
