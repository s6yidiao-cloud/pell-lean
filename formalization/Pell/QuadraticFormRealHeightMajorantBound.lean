import Pell.QuadraticFormRepresentationRealHeightWindow

/-!
# Coefficient bounds for the quadratic-form real-height majorant

This file converts a common absolute bound on the three coefficients of an
integral binary quadratic form into a coarse bound for its discriminant square
root and hence for `formIdealVectorRealHeightMajorant`.  The constants `3` and
`6` are intentionally round: the discriminant identity gives the sharper
square bound `D ≤ 5 K²`, while `sqrt 5 ≤ 3` and the added `1` in the height
majorant are absorbed using `K, X ≥ 1`.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

/-- A common coefficient bound `K` controls the square root of a nonnegative
discriminant by `3 K`. -/
theorem sqrt_discriminant_le_three_mul_of_coeff_abs_le
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) {K : ℝ} (hK : 0 ≤ K)
    (ha : |(Q.a : ℝ)| ≤ K) (hb : |(Q.b : ℝ)| ≤ K)
    (hc : |(Q.c : ℝ)| ≤ K) :
    Real.sqrt (D : ℝ) ≤ 3 * K := by
  have hDreal : (0 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hdisc :
      (Q.b : ℝ) ^ 2 - 4 * (Q.a : ℝ) * (Q.c : ℝ) = (D : ℝ) := by
    exact_mod_cast hQ
  have hbSq : (Q.b : ℝ) ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hacAbs : |(Q.a : ℝ) * (Q.c : ℝ)| ≤ K * K := by
    rw [abs_mul]
    exact mul_le_mul ha hc (abs_nonneg _) hK
  have hacLower : -(K ^ 2) ≤ (Q.a : ℝ) * (Q.c : ℝ) := by
    have := (neg_le_of_abs_le hacAbs)
    simpa only [pow_two] using this
  have hDupper : (D : ℝ) ≤ 5 * K ^ 2 := by
    rw [← hdisc]
    nlinarith
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [sq_nonneg K]

/-- Once both the coefficient bound and coordinate radius are at least one,
the elementary real-height majorant is at most `6 K X`. -/
theorem formIdealVectorRealHeightMajorant_le_six_mul
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) {K X : ℝ}
    (hK : 1 ≤ K) (hX : 1 ≤ X)
    (ha : |(Q.a : ℝ)| ≤ K) (hb : |(Q.b : ℝ)| ≤ K)
    (hc : |(Q.c : ℝ)| ≤ K) :
    formIdealVectorRealHeightMajorant D Q X ≤ 6 * K * X := by
  have hsqrt : Real.sqrt (D : ℝ) ≤ 3 * K :=
    sqrt_discriminant_le_three_mul_of_coeff_abs_le
      D hD Q hQ (zero_le_one.trans hK) ha hb hc
  have hcoef :
      |(Q.a : ℝ)| + |(Q.b : ℝ)| + Real.sqrt (D : ℝ) ≤ 5 * K := by
    linarith
  have hXnonneg : 0 ≤ X := hX.trans' zero_le_one
  have hscaled :
      (|(Q.a : ℝ)| + |(Q.b : ℝ)| + Real.sqrt (D : ℝ)) * X ≤
        5 * K * X := by
    exact mul_le_mul_of_nonneg_right hcoef hXnonneg
  have hKX : 1 ≤ K * X := by
    have hKm : 0 ≤ K - 1 := by linarith
    have hXm : 0 ≤ X - 1 := by linarith
    nlinarith [mul_nonneg hKm hXm]
  unfold formIdealVectorRealHeightMajorant
  nlinarith

/-- Logarithmic form of the coarse real-height majorant bound. -/
theorem log_formIdealVectorRealHeightMajorant_le_log_six_add
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) {K X : ℝ}
    (hK : 1 ≤ K) (hX : 1 ≤ X)
    (ha : |(Q.a : ℝ)| ≤ K) (hb : |(Q.b : ℝ)| ≤ K)
    (hc : |(Q.c : ℝ)| ≤ K) :
    Real.log (formIdealVectorRealHeightMajorant D Q X) ≤
      Real.log 6 + Real.log K + Real.log X := by
  have hheightPos : 0 < formIdealVectorRealHeightMajorant D Q X :=
    formIdealVectorRealHeightMajorant_pos D hD Q (hX.trans' zero_le_one)
  have hheightUpper :
      formIdealVectorRealHeightMajorant D Q X ≤ 6 * K * X :=
    formIdealVectorRealHeightMajorant_le_six_mul
      D hD Q hQ hK hX ha hb hc
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  calc
    Real.log (formIdealVectorRealHeightMajorant D Q X) ≤
        Real.log (6 * K * X) :=
      Real.log_le_log hheightPos hheightUpper
    _ = Real.log 6 + Real.log K + Real.log X := by
      rw [Real.log_mul (mul_ne_zero (by norm_num) hKpos.ne') hXpos.ne',
        Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hKpos.ne']

end
end IntegralBinaryQuadraticForm
end PellPaper
