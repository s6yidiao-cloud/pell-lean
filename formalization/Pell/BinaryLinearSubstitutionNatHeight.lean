import Pell.BinaryLinearSubstitutionHeight

/-!
# Positive natural heights for binary linear substitutions

The analytic residual route produces real coefficient and matrix-entry bounds,
whereas the squarefree-certificate constructor expects a positive natural
coefficient height.  This file makes both ceiling losses explicit and packages
the resulting natural height for `K(W*x)`.
-/

namespace PellPaper

noncomputable section

/-- A positive natural ceiling, including at the zero boundary. -/
def positiveNatCeil (x : ℝ) : ℕ := max 1 ⌈x⌉₊

theorem positiveNatCeil_pos (x : ℝ) : 0 < positiveNatCeil x := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- A nonnegative real is bounded by its positive natural ceiling. -/
theorem le_positiveNatCeil (x : ℝ) : x ≤ (positiveNatCeil x : ℝ) := by
  exact (Nat.le_ceil x).trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)

/-- The positive-ceiling convention costs at most one. -/
theorem positiveNatCeil_le_add_one {x : ℝ} (hx : 0 ≤ x) :
    (positiveNatCeil x : ℝ) ≤ x + 1 := by
  rw [positiveNatCeil]
  push_cast
  exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le

/-- The explicit positive natural coefficient height used after substituting
an integral two-by-two matrix into a degree-`d` binary form. -/
def binaryLinearSubstitutionNatHeight (d : ℕ) (H L : ℝ) : ℕ :=
  (d + 1) * positiveNatCeil H * (2 * positiveNatCeil L) ^ d

theorem binaryLinearSubstitutionNatHeight_pos (d : ℕ) (H L : ℝ) :
    0 < binaryLinearSubstitutionNatHeight d H L := by
  dsimp [binaryLinearSubstitutionNatHeight]
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.succ_pos d) (positiveNatCeil_pos H))
    (pow_pos (Nat.mul_pos (by omega) (positiveNatCeil_pos L)) d)

/-- Real coefficient and entry bounds give the corresponding integral bounds
at the two positive natural ceilings. -/
theorem abs_coeff_binaryLinearSubstitution_le_natHeight
    (W : Matrix (Fin 2) (Fin 2) ℤ)
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (H L : ℝ)
    (hK : K.IsHomogeneous d)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H)
    (hW : ∀ i j, |((W i j : ℤ) : ℝ)| ≤ L)
    (e : Fin 2 →₀ ℕ) :
    |(binaryLinearSubstitution W K).coeff e| ≤
      (binaryLinearSubstitutionNatHeight d H L : ℤ) := by
  have hcoeffZ : ∀ f, |K.coeff f| ≤ (positiveNatCeil H : ℤ) := by
    intro f
    have hf : |((K.coeff f : ℤ) : ℝ)| ≤ (positiveNatCeil H : ℝ) :=
      (hcoeff f).trans (le_positiveNatCeil H)
    exact_mod_cast hf
  have hWZ : ∀ i j, |W i j| ≤ (positiveNatCeil L : ℤ) := by
    intro i j
    have hij : |((W i j : ℤ) : ℝ)| ≤ (positiveNatCeil L : ℝ) :=
      (hW i j).trans (le_positiveNatCeil L)
    exact_mod_cast hij
  have h := abs_coeff_binaryLinearSubstitution_le W K d
    (positiveNatCeil H : ℤ) (positiveNatCeil L : ℤ) hK
    (by positivity) (by positivity) hcoeffZ hWZ e
  simpa [binaryLinearSubstitutionNatHeight] using h

/-- The chosen natural height has the exact two-ceiling real cost. -/
theorem binaryLinearSubstitutionNatHeight_le
    (d : ℕ) {H L : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) :
    (binaryLinearSubstitutionNatHeight d H L : ℝ) ≤
      ((d : ℝ) + 1) * (H + 1) * (2 * (L + 1)) ^ d := by
  have hHC := positiveNatCeil_le_add_one hH
  have hLC := positiveNatCeil_le_add_one hL
  have hH0 : 0 ≤ (positiveNatCeil H : ℝ) := by positivity
  have hL0 : 0 ≤ (positiveNatCeil L : ℝ) := by positivity
  dsimp [binaryLinearSubstitutionNatHeight]
  push_cast
  gcongr

/-- The same two ceiling losses in logarithmic form, ready for the
squarefree-certificate and good-prime budgets. -/
theorem log_binaryLinearSubstitutionNatHeight_le
    (d : ℕ) {H L : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) :
    Real.log (binaryLinearSubstitutionNatHeight d H L : ℝ) ≤
      Real.log ((d : ℝ) + 1) + Real.log (H + 1) +
        (d : ℝ) * (Real.log 2 + Real.log (L + 1)) := by
  have hheight := binaryLinearSubstitutionNatHeight_le d hH hL
  have hleft : 0 < (binaryLinearSubstitutionNatHeight d H L : ℝ) := by
    exact_mod_cast binaryLinearSubstitutionNatHeight_pos d H L
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hHp : 0 < H + 1 := by linarith
  have hLp : 0 < L + 1 := by linarith
  calc
    Real.log (binaryLinearSubstitutionNatHeight d H L : ℝ) ≤
        Real.log (((d : ℝ) + 1) * (H + 1) * (2 * (L + 1)) ^ d) :=
      Real.log_le_log hleft hheight
    _ = Real.log ((d : ℝ) + 1) + Real.log (H + 1) +
        (d : ℝ) * (Real.log 2 + Real.log (L + 1)) := by
      rw [Real.log_mul (mul_ne_zero hd.ne' hHp.ne')
          (pow_ne_zero _ (mul_ne_zero (by norm_num) hLp.ne')),
        Real.log_mul hd.ne' hHp.ne', Real.log_pow,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLp.ne']

end
end PellPaper
