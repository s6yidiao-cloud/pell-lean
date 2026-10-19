import Pell.LocalRatioIdentity
import Pell.ShiftedSquareReduction

/-!
# Auxiliary parabola factors and the divisor reduction

The auxiliary-curve argument treats separately a factor of the form
`a * (t - s^2) - b`.  At a separated Pell factor tuple, its affine
vanishing is equivalent to the displayed bihomogeneous relation

`a * (e^2 v - d^2 u) - b * e^2 u = 0`.

Combining this with the exact difference equation produces the finite
divisor relation `b * e^2 * u = a * h`, while retaining the independent
shifted-square identity.  This module is entirely algebraic and makes no
curve-counting assertion.
-/

namespace PellPaper

noncomputable section

/-- Affine evaluation of the special auxiliary factor
`a * (t - s^2) - b` at the rational slopes `s = d/e`, `t = v/u`. -/
def auxiliaryParabolaAffineLineEval (a b : ℤ) (d e u v : ℕ) : ℚ :=
  (a : ℚ) * ((v : ℚ) / (u : ℚ) - ((d : ℚ) / (e : ℚ)) ^ 2) - (b : ℚ)

/-- The bihomogenization of `a * (t - s^2) - b` at the integral slope
coordinates. -/
def auxiliaryParabolaHomogeneousLineEval (a b : ℤ) (d e u v : ℕ) : ℤ :=
  a * ((e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u) -
    b * ((e : ℤ) ^ 2 * u)

/-- Exact dehomogenization identity for the special affine parabola line. -/
theorem auxiliaryParabolaAffineLineEval_eq_homogeneous_div
    (a b : ℤ) (d e u v : ℕ) (he : 0 < e) (hu : 0 < u) :
    auxiliaryParabolaAffineLineEval a b d e u v =
      (auxiliaryParabolaHomogeneousLineEval a b d e u v : ℚ) /
        ((e : ℚ) ^ 2 * (u : ℚ)) := by
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt he
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hu
  unfold auxiliaryParabolaAffineLineEval auxiliaryParabolaHomogeneousLineEval
  push_cast
  field_simp [heq, huq]

/-- Thus affine vanishing of the special factor is equivalent to vanishing
of its integral bihomogenization. -/
theorem auxiliaryParabolaAffineLineEval_eq_zero_iff_homogeneous_eq_zero
    (a b : ℤ) (d e u v : ℕ) (he : 0 < e) (hu : 0 < u) :
    auxiliaryParabolaAffineLineEval a b d e u v = 0 ↔
      auxiliaryParabolaHomogeneousLineEval a b d e u v = 0 := by
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt he
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hu
  have hden : ((e : ℚ) ^ 2 * (u : ℚ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ heq) huq
  rw [auxiliaryParabolaAffineLineEval_eq_homogeneous_div a b d e u v he hu]
  constructor
  · intro hzero
    have hnum : (auxiliaryParabolaHomogeneousLineEval a b d e u v : ℚ) = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right hden
    exact_mod_cast hnum
  · intro hzero
    norm_num [hzero]

/-- Combining the homogeneous auxiliary relation with the Pell factor
difference gives the exact divisor identity used for the special curve
components. -/
theorem auxiliaryParabolaHomogeneousLineEval_divisor_identity
    {a b h : ℤ} {d e u v : ℕ}
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    b * ((e : ℤ) ^ 2 * u) = a * h := by
  unfold auxiliaryParabolaHomogeneousLineEval at haux
  rw [hdiff] at haux
  linarith

/-- The positive squarefree denominator factor is an integral divisor of
the fixed auxiliary product `a * h`. -/
theorem e_sq_mul_u_dvd_auxiliaryParabolaProduct
    {a b h : ℤ} {d e u v : ℕ}
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    ((e : ℤ) ^ 2 * u) ∣ a * h := by
  refine ⟨b, ?_⟩
  rw [← auxiliaryParabolaHomogeneousLineEval_divisor_identity haux hdiff]
  ring

/-- The intercept coefficient is also a divisor of `a * h`. -/
theorem auxiliaryParabolaIntercept_dvd_product
    {a b h : ℤ} {d e u v : ℕ}
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    b ∣ a * h := by
  refine ⟨(e : ℤ) ^ 2 * u, ?_⟩
  exact (auxiliaryParabolaHomogeneousLineEval_divisor_identity haux hdiff).symm

/-- A genuinely nonzero multiple of `t - s^2` cannot vanish at a separated
Pell factor tuple with nonzero difference.  This is the integral counterpart
of removing the `t = s^2` component before the curve count. -/
theorem auxiliaryParabolaIntercept_ne_zero_of_homogeneous_vanishing
    {a b h : ℤ} {d e u v : ℕ} (ha : a ≠ 0) (hh : h ≠ 0)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    b ≠ 0 := by
  intro hb
  unfold auxiliaryParabolaHomogeneousLineEval at haux
  rw [hdiff, hb] at haux
  exact (mul_ne_zero ha hh) (by linarith)

/-- The special auxiliary relation supplies both the shifted-square equation
and the divisor data in one package. -/
theorem auxiliaryParabolaHomogeneousLineEval_to_shiftedSquare_divisor
    {a b h : ℤ} {d e u v : ℕ}
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (d : ℤ) ^ 2 * (shiftedSquareW u v : ℤ) =
        (shiftedSquareN e v) ^ 2 + shiftedSquareA h v ∧
      b * ((e : ℤ) ^ 2 * u) = a * h ∧
      ((e : ℤ) ^ 2 * u) ∣ a * h ∧ b ∣ a * h := by
  exact ⟨shifted_square_identity hdiff,
    auxiliaryParabolaHomogeneousLineEval_divisor_identity haux hdiff,
    e_sq_mul_u_dvd_auxiliaryParabolaProduct haux hdiff,
    auxiliaryParabolaIntercept_dvd_product haux hdiff⟩

/-- Source-facing version for a bounded dyadic factor tuple.  In addition to
the shifted-square and divisor identities, it records that the shift is
nonzero and has the required explicit size. -/
theorem auxiliaryParabolaHomogeneousLineEval_to_shiftedSquare_divisor_of_dyadicFactorCondition
    {θ : ℝ} {Y d e u v : ℕ} {a b h : ℤ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (d : ℤ) ^ 2 * (shiftedSquareW u v : ℤ) =
        (shiftedSquareN e v) ^ 2 + shiftedSquareA h v ∧
      shiftedSquareA h v ≠ 0 ∧ |shiftedSquareA h v| ≤ 2 * (v : ℤ) ∧
      b * ((e : ℤ) ^ 2 * u) = a * h ∧
      ((e : ℤ) ^ 2 * u) ∣ a * h ∧ b ∣ a * h := by
  have hh : IsSignedDyadicDifference h :=
    isSignedDyadicDifference_of_dyadicFactorCondition hcond hdiff
  rcases hcond with ⟨_, _, _, hv, _⟩
  refine ⟨shifted_square_identity hdiff, shiftedSquareA_ne_zero hh hv,
    shiftedSquareA_abs_le_two_mul hh, ?_⟩
  exact ⟨auxiliaryParabolaHomogeneousLineEval_divisor_identity haux hdiff,
    e_sq_mul_u_dvd_auxiliaryParabolaProduct haux hdiff,
    auxiliaryParabolaIntercept_dvd_product haux hdiff⟩

end

end PellPaper
