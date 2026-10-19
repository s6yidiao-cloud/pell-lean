import Pell.ShiftedSquareReduction
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Real heights from literal weighted-square bounds

For positive integral parameters and coordinates, the real quadratic value
`v*e + d*sqrt(u*v)` lies between one and `2*sqrt(v*X)` whenever both
weighted squares `v*e^2` and `u*d^2` are at most `X`.
The actual signed difference then supplies the second weighted-square bound
from the first at the slightly enlarged cutoff `X+2`. These are scalar
height bounds, not an orbit or point-counting theorem.
-/

namespace PellPaper

/-- Positive integral data and the two actual weighted-square upper bounds
give a lower and upper bound for the literal real quadratic value. -/
theorem fixedNorm_real_value_bounds_of_weighted_squares
    (u v d e : ℤ) (X : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (he : 0 < e)
    (heX : (v : ℝ) * (e : ℝ) ^ 2 ≤ X)
    (hdX : (u : ℝ) * (d : ℝ) ^ 2 ≤ X) :
    1 ≤ (v : ℝ) * e + (d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ∧
      (v : ℝ) * e + (d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ≤
        2 * Real.sqrt ((v : ℝ) * X) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have huvR : (0 : ℝ) ≤ ((u * v : ℤ) : ℝ) := by
    exact_mod_cast (mul_pos hu hv).le
  constructor
  · have hve : (1 : ℝ) ≤ (v : ℝ) * e := by
      simpa using mul_le_mul hv1 he1 (by norm_num : (0 : ℝ) ≤ 1) hvR.le
    exact hve.trans (le_add_of_nonneg_right
      (mul_nonneg hdR.le (Real.sqrt_nonneg _)))
  · have hve : ((v : ℝ) * e) ^ 2 ≤ (v : ℝ) * X := by
      calc
        ((v : ℝ) * e) ^ 2 = (v : ℝ) * ((v : ℝ) * (e : ℝ) ^ 2) := by ring
        _ ≤ (v : ℝ) * X := mul_le_mul_of_nonneg_left heX hvR.le
    have hdr : ((d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) ^ 2 ≤
        (v : ℝ) * X := by
      calc
        ((d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) ^ 2 =
            (v : ℝ) * ((u : ℝ) * (d : ℝ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt huvR, Int.cast_mul]
          ring
        _ ≤ (v : ℝ) * X := mul_le_mul_of_nonneg_left hdX hvR.le
    have hsum := add_le_add (Real.le_sqrt_of_sq_le hve) (Real.le_sqrt_of_sq_le hdr)
    linarith

/-- On one of the four actual signed norm levels, the first weighted-square
cutoff alone bounds the literal real quadratic value. The other square is
derived from the norm equation and can exceed the original cutoff by two. -/
theorem fixedNorm_real_value_bounds_of_signed_difference
    (u v d e h : ℤ) (X : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (he : 0 < e)
    (hh : IsSignedDyadicDifference h)
    (hn : v * e ^ 2 - u * d ^ 2 = h)
    (heX : (v : ℝ) * (e : ℝ) ^ 2 ≤ X) :
    1 ≤ (v : ℝ) * e + (d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ∧
      (v : ℝ) * e + (d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ≤
        2 * Real.sqrt ((v : ℝ) * (X + 2)) := by
  have hlow : (-2 : ℝ) ≤ h := by
    rcases hh with rfl | rfl | rfl | rfl <;> norm_num
  have hnR : (v : ℝ) * (e : ℝ) ^ 2 - (u : ℝ) * (d : ℝ) ^ 2 = (h : ℝ) := by
    exact_mod_cast hn
  apply fixedNorm_real_value_bounds_of_weighted_squares u v d e (X + 2) hu hv hd he
  · linarith
  · linarith

end PellPaper
