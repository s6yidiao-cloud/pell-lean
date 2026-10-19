import Pell.DyadicCountingReduction

/-!
# The shifted-square reduction for separated Pell factors

For a separated factor equation
`e^2 v - d^2 u = h`, multiplication by `v` gives the shifted-square
equation used in the determinant argument:
`d^2(uv) = (ev)^2 - hv`.

This file records that change of variables with all coercions explicit.  It
does not use, or assert, any minimality statement about the resulting
shifted-square parameter.
-/

namespace PellPaper

/-- The four signed differences arising from the oriented Pell
factorization. -/
def IsSignedDyadicDifference (h : ℤ) : Prop :=
  h = 1 ∨ h = -1 ∨ h = 2 ∨ h = -2

/-- The square coordinate in the shifted-square equation. -/
def shiftedSquareN (e v : ℕ) : ℤ :=
  (e : ℤ) * (v : ℤ)

/-- The (nonzero) shift in the shifted-square equation. -/
def shiftedSquareA (h : ℤ) (v : ℕ) : ℤ :=
  -h * (v : ℤ)

/-- The radicand coordinate in the shifted-square equation. -/
def shiftedSquareW (u v : ℕ) : ℕ :=
  u * v

/-- A signed difference furnished by `DyadicFactorCondition` remains signed
after naming its value `h`. -/
theorem isSignedDyadicDifference_of_dyadicFactorCondition
    {θ : ℝ} {Y d e u v : ℕ} {h : ℤ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    IsSignedDyadicDifference h := by
  rcases hcond with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsign, _⟩
  rcases hsign with hsign | hsign | hsign | hsign
  · exact Or.inl (hdiff.symm.trans hsign)
  · exact Or.inr (Or.inl (hdiff.symm.trans hsign))
  · exact Or.inr (Or.inr (Or.inl (hdiff.symm.trans hsign)))
  · exact Or.inr (Or.inr (Or.inr (hdiff.symm.trans hsign)))

/-- The elementary integer identity behind the shifted-square substitution. -/
theorem shifted_square_integer_identity {d e u v : ℕ} {h : ℤ}
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (d : ℤ) ^ 2 * ((u : ℤ) * v) =
      ((e : ℤ) * v) ^ 2 + (-h * v) := by
  have hmain : (d : ℤ) ^ 2 * u = (e : ℤ) ^ 2 * v - h := by
    linarith
  calc
    (d : ℤ) ^ 2 * ((u : ℤ) * v) = ((d : ℤ) ^ 2 * u) * v := by ring
    _ = ((e : ℤ) ^ 2 * v - h) * v := by rw [hmain]
    _ = ((e : ℤ) * v) ^ 2 + (-h * v) := by ring

/-- In the named variables, the separated factor equation becomes a shifted
square equation. -/
theorem shifted_square_identity {d e u v : ℕ} {h : ℤ}
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (d : ℤ) ^ 2 * (shiftedSquareW u v : ℤ) =
      (shiftedSquareN e v) ^ 2 + shiftedSquareA h v := by
  simpa only [shiftedSquareW, shiftedSquareN, shiftedSquareA, Nat.cast_mul]
    using shifted_square_integer_identity hdiff

/-- None of the four signed differences is zero. -/
theorem isSignedDyadicDifference_ne_zero {h : ℤ}
    (hh : IsSignedDyadicDifference h) : h ≠ 0 := by
  rcases hh with rfl | rfl | rfl | rfl <;> norm_num

/-- The shift is nonzero whenever the squarefree coordinate is positive. -/
theorem shiftedSquareA_ne_zero {h : ℤ} {v : ℕ}
    (hh : IsSignedDyadicDifference h) (hv : 0 < v) :
    shiftedSquareA h v ≠ 0 := by
  unfold shiftedSquareA
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (isSignedDyadicDifference_ne_zero hh)
  · exact_mod_cast Nat.ne_of_gt hv

/-- Each possible shift has absolute value at most twice the `v` coordinate. -/
theorem shiftedSquareA_abs_le_two_mul {h : ℤ} {v : ℕ}
    (hh : IsSignedDyadicDifference h) :
    |shiftedSquareA h v| ≤ 2 * (v : ℤ) := by
  have hvnonneg : 0 ≤ (v : ℤ) := by positivity
  unfold shiftedSquareA
  rw [abs_mul, abs_neg, abs_of_nonneg hvnonneg]
  apply mul_le_mul_of_nonneg_right _ hvnonneg
  rcases hh with rfl | rfl | rfl | rfl <;> norm_num

/-- The dyadic condition supplies positivity of `v`, so every corresponding
shift is nonzero. -/
theorem shiftedSquareA_ne_zero_of_dyadicFactorCondition
    {θ : ℝ} {Y d e u v : ℕ} {h : ℤ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    shiftedSquareA h v ≠ 0 := by
  have hh := isSignedDyadicDifference_of_dyadicFactorCondition hcond hdiff
  rcases hcond with ⟨_, _, _, hv, _⟩
  exact shiftedSquareA_ne_zero hh hv

/-- The full arithmetic reduction supplied by a dyadic factor tuple. -/
theorem shifted_square_reduction_of_dyadicFactorCondition
    {θ : ℝ} {Y d e u v : ℕ} {h : ℤ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (d : ℤ) ^ 2 * (shiftedSquareW u v : ℤ) =
      (shiftedSquareN e v) ^ 2 + shiftedSquareA h v ∧
    shiftedSquareA h v ≠ 0 ∧
    |shiftedSquareA h v| ≤ 2 * (v : ℤ) := by
  refine ⟨shifted_square_identity hdiff,
    shiftedSquareA_ne_zero_of_dyadicFactorCondition hcond hdiff, ?_⟩
  exact shiftedSquareA_abs_le_two_mul
    (isSignedDyadicDifference_of_dyadicFactorCondition hcond hdiff)

/-- For the `h = 1` branch, the shift is not `-1` provided the genuinely
extra condition `1 < v` holds.  No fundamental-minimality assertion is used. -/
theorem shiftedSquareA_ne_neg_one_of_difference_one {v : ℕ}
    (hv : 1 < v) : shiftedSquareA 1 v ≠ -1 := by
  have hvz : (1 : ℤ) < v := by exact_mod_cast hv
  intro ha
  unfold shiftedSquareA at ha
  nlinarith

end PellPaper
