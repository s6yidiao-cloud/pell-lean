import Pell.BinaryProjectiveDerivativeResultantHeight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Logarithmic height of the projective derivative resultant

This file converts the explicit factorial/Leibniz bound for the fixed
projective derivative resultant into the logarithmic form needed by the
good-prime annulus.  A second theorem includes the literal factor `2 * c`
used in the manuscript's bad-reduction certificate.
-/

namespace PellPaper

noncomputable section

/-- The finite factorial/Leibniz resultant bound, expressed as an exact
logarithmic inequality.  Nonvanishing is retained explicitly because this
is the form used in the good-prime budget. -/
theorem log_natAbs_binaryProjectiveDerivativeResultant_le
    (J : MvPolynomial (Fin 2) ℤ) (j H : ℕ)
    (hJ : J.IsHomogeneous j) (hj : 0 < j) (hH : 0 < H)
    (hcoeff : ∀ d, |J.coeff d| ≤ (H : ℤ))
    (hres : binaryProjectiveDerivativeResultant J j ≠ 0) :
    Real.log ((binaryProjectiveDerivativeResultant J j).natAbs : ℝ) ≤
      Real.log ((2 * (j - 1)).factorial : ℝ) +
        (2 * (j - 1) : ℕ) *
          (2 * Real.log (j : ℝ) + Real.log (H : ℝ)) := by
  let R : ℤ := binaryProjectiveDerivativeResultant J j
  let r : ℕ := 2 * (j - 1)
  have hfinite : |R| ≤ (r.factorial : ℤ) *
      (((j : ℤ) ^ 2 * (H : ℤ)) ^ r) := by
    simpa only [R, r] using
      abs_binaryProjectiveDerivativeResultant_le_factorial_mul_pow
        J j hJ hj (by positivity) hcoeff
  have hfiniteR : (R.natAbs : ℝ) ≤
      (r.factorial : ℝ) * (((j : ℝ) ^ 2 * (H : ℝ)) ^ r) := by
    have hfinite' : (R.natAbs : ℤ) ≤ (r.factorial : ℤ) *
        (((j : ℤ) ^ 2 * (H : ℤ)) ^ r) := by
      simpa only [Int.natCast_natAbs] using hfinite
    exact_mod_cast hfinite'
  have hleft : 0 < (R.natAbs : ℝ) := by
    exact_mod_cast (Int.natAbs_pos.mpr (by simpa only [R] using hres))
  have hlog := Real.log_le_log hleft hfiniteR
  calc
    Real.log ((binaryProjectiveDerivativeResultant J j).natAbs : ℝ) =
        Real.log (R.natAbs : ℝ) := by rfl
    _ ≤ Real.log ((r.factorial : ℝ) *
        (((j : ℝ) ^ 2 * (H : ℝ)) ^ r)) := hlog
    _ = Real.log (r.factorial : ℝ) +
        (r : ℝ) * (2 * Real.log (j : ℝ) + Real.log (H : ℝ)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    _ = Real.log ((2 * (j - 1)).factorial : ℝ) +
        (2 * (j - 1) : ℕ) *
          (2 * Real.log (j : ℝ) + Real.log (H : ℝ)) := by rfl

/-- The logarithmic height of the literal certificate
`2 * c * binaryProjectiveDerivativeResultant J j`.  This is the direct
product form consumed by the good-prime annulus, while keeping both
nonvanishing conditions explicit. -/
theorem log_natAbs_two_mul_content_mul_binaryProjectiveDerivativeResultant_le
    (J : MvPolynomial (Fin 2) ℤ) (j H : ℕ) (c : ℤ)
    (hJ : J.IsHomogeneous j) (hj : 0 < j) (hH : 0 < H)
    (hcoeff : ∀ d, |J.coeff d| ≤ (H : ℤ))
    (hc : c ≠ 0) (hres : binaryProjectiveDerivativeResultant J j ≠ 0) :
    Real.log ((2 * c * binaryProjectiveDerivativeResultant J j).natAbs : ℝ) ≤
      Real.log 2 + Real.log (c.natAbs : ℝ) +
        Real.log ((2 * (j - 1)).factorial : ℝ) +
          (2 * (j - 1) : ℕ) *
            (2 * Real.log (j : ℝ) + Real.log (H : ℝ)) := by
  let R : ℤ := binaryProjectiveDerivativeResultant J j
  have hcpos : 0 < (c.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hc
  have hrpos : 0 < (R.natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (by simpa only [R] using hres)
  have hproduct :
      Real.log ((2 * c * R).natAbs : ℝ) =
        Real.log 2 + Real.log (c.natAbs : ℝ) +
          Real.log (R.natAbs : ℝ) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    norm_num
  rw [show binaryProjectiveDerivativeResultant J j = R by rfl, hproduct]
  have hlog := log_natAbs_binaryProjectiveDerivativeResultant_le
    J j H hJ hj hH hcoeff hres
  change Real.log 2 + Real.log (c.natAbs : ℝ) +
      Real.log (R.natAbs : ℝ) ≤ _
  change Real.log (R.natAbs : ℝ) ≤ _ at hlog
  linarith

end
end PellPaper
