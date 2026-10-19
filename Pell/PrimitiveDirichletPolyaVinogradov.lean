import Pell.PrimitiveDirichletGaussSumNorm
import Pell.ZModExponentialWindowBound
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Pólya--Vinogradov for primitive nonprincipal characters

Inverse discrete Fourier transformation, the primitive Gauss-sum norm,
and the proved finite-exponential window bound give a character-sum bound
uniform in both interval start and length. The modulus need not be prime.
Primitivity and nonprincipality remain explicit; no imprimitive-character
bound or selected-character primitivity is asserted here.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

private theorem sum_zmod_eq_sum_range
    {q : ℕ} [NeZero q] {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ k : ZMod q, f k) = ∑ k ∈ Finset.range q, f (k : ZMod q) := by
  classical
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg f (ZMod.natCast_zmod_val k).symm

/-- Actual primitive nonprincipal character sums over arbitrary finite
windows satisfy the square-root times logarithm bound at every nonzero
level. The starting residue and window length are unrestricted. -/
theorem primitiveDirichletCharacter_sum_range_norm_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (a : ZMod q) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, χ (a + (n : ZMod q))‖ ≤
      Real.sqrt (q : ℝ) * (1 + Real.log q) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let F : ZMod q → ℂ := ZMod.dft (χ : ZMod q → ℂ)
  let W : ZMod q → ℂ := fun k =>
    ∑ n ∈ Finset.range L, ZMod.stdAddChar (k * (a + (n : ZMod q)))
  have hFzero : F 0 = 0 := by
    dsimp [F]
    rw [ZMod.dft_apply_zero]
    exact MulChar.sum_eq_zero_of_ne_one hne
  have hFnorm (k : ZMod q) : ‖F k‖ ≤ Real.sqrt (q : ℝ) := by
    dsimp [F]
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum, norm_mul,
      primitiveDirichletCharacter_gaussSum_norm χ hprim]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      ((χ⁻¹ : DirichletCharacter ℂ q).norm_le_one (-k)) (Real.sqrt_nonneg _)
  have hinv (x : ZMod q) : χ x =
      (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.stdAddChar (k * x) * F k := by
    have h := congrFun (ZMod.dft.symm_apply_apply (χ : ZMod q → ℂ)) x
    simpa only [ZMod.invDFT_apply, smul_eq_mul] using h.symm
  have hsum : (∑ n ∈ Finset.range L, χ (a + (n : ZMod q))) =
      (q : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 q, F (k : ZMod q) * W (k : ZMod q) := by
    calc
      (∑ n ∈ Finset.range L, χ (a + (n : ZMod q))) =
          (q : ℂ)⁻¹ * ∑ n ∈ Finset.range L,
            ∑ k : ZMod q, ZMod.stdAddChar (k * (a + (n : ZMod q))) * F k := by
        simp_rw [hinv]
        rw [Finset.mul_sum]
      _ = (q : ℂ)⁻¹ * ∑ k : ZMod q, F k * W k := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [W]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = (q : ℂ)⁻¹ * ∑ k ∈ Finset.range q, F (k : ZMod q) * W (k : ZMod q) := by
        rw [sum_zmod_eq_sum_range]
      _ = _ := by
        rw [Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero (NeZero.ne q))]
        simp only [Nat.cast_zero, hFzero, zero_mul, zero_add]
  have hwindow : (∑ k ∈ Finset.Ico 1 q, ‖W (k : ZMod q)‖) ≤
      (q : ℝ) * (1 + Real.log q) := by
    exact sum_norm_stdAddChar_sum_range_le a L
  rw [hsum, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∑ k ∈ Finset.Ico 1 q, F (k : ZMod q) * W (k : ZMod q)‖ ≤
        (q : ℝ)⁻¹ * ∑ k ∈ Finset.Ico 1 q, ‖F (k : ZMod q) * W (k : ZMod q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hq.le)
    _ ≤ (q : ℝ)⁻¹ * ∑ k ∈ Finset.Ico 1 q, Real.sqrt (q : ℝ) * ‖W (k : ZMod q)‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hFnorm _) (norm_nonneg _)
    _ = ((q : ℝ)⁻¹ * Real.sqrt (q : ℝ)) * ∑ k ∈ Finset.Ico 1 q, ‖W (k : ZMod q)‖ := by
      rw [← Finset.mul_sum, mul_assoc]
    _ ≤ ((q : ℝ)⁻¹ * Real.sqrt (q : ℝ)) * ((q : ℝ) * (1 + Real.log q)) :=
      mul_le_mul_of_nonneg_left hwindow (mul_nonneg (inv_nonneg.mpr hq.le) (Real.sqrt_nonneg _))
    _ = Real.sqrt (q : ℝ) * (1 + Real.log q) := by
      field_simp

/-- A literal natural-number interval version of the primitive
Pólya--Vinogradov bound, including empty intervals. -/
theorem primitiveDirichletCharacter_sum_Ico_norm_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (m n : ℕ) :
    ‖∑ j ∈ Finset.Ico m n, χ (j : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (1 + Real.log q) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add, add_comm] using
    primitiveDirichletCharacter_sum_range_norm_le χ hprim hne (m : ZMod q) (n - m)

end
end PellPaper
