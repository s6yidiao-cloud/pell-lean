import Pell.JacobiDirichletCharacterNonprincipal
import Pell.NonprincipalDirichletPolyaVinogradov

/-!
# Cancellation for actual numerator-Jacobi prefixes

The modulus is any positive odd nonsquare, not necessarily squarefree.
This is the literal real character correlation used in the finite second
moment; nonprincipality and the character-sum estimate are discharged here.
-/

open scoped BigOperators

namespace PellPaper

/-- A real Jacobi prefix inherits the all-nonprincipal character bound. -/
theorem abs_sum_jacobiSym_le_of_odd_not_isSquare
    (q X : ℕ) (hq : 0 < q) (hodd : Odd q) (hns : ¬ IsSquare q) :
    |∑ d ∈ Finset.Icc 1 X, (jacobiSym (d : ℤ) q : ℝ)| ≤
      2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hq1 : 1 < q := by
    have hne : q ≠ 1 := by
      intro h
      exact hns (h ▸ IsSquare.one)
    omega
  let _ : Fact (1 < q) := ⟨hq1⟩
  let _ : NeZero q := ⟨hq.ne'⟩
  have hχ : jacobiDirichletCharacterC q ≠ 1 :=
    jacobiDirichletCharacterC_ne_one_of_odd_not_isSquare q hq hodd hns
  have hpv := nonprincipalDirichletCharacter_prefix_norm_le
    (jacobiDirichletCharacterC q) hχ X
  have hcast : (∑ d ∈ Finset.Icc 1 X,
      jacobiDirichletCharacterC q (d : ZMod q)) =
      Complex.ofReal (∑ d ∈ Finset.Icc 1 X, (jacobiSym (d : ℤ) q : ℝ)) := by
    simp only [jacobiDirichletCharacterC_apply_natCast,
      Complex.ofReal_sum, Complex.ofReal_intCast]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hpv
  exact hpv

/-- Uniform cancellation for nonsquare products in the truncation box. -/
theorem abs_sum_jacobiSym_mul_le_truncation
    (n m N X : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hnN : n ≤ N) (hmN : m ≤ N) (hodd : Odd (n * m))
    (hns : ¬ IsSquare (n * m)) :
    |∑ d ∈ Finset.Icc 1 X, (jacobiSym (d : ℤ) (n * m) : ℝ)| ≤
      2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)) := by
  have hN : 0 < N := hn.trans_le hnN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : (0 : ℝ) < (n * m : ℕ) := by exact_mod_cast Nat.mul_pos hn hm
  have hprodN : ((n * m : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast (show n * m ≤ N ^ 2 by nlinarith)
  have hsqrt : Real.sqrt ((n * m : ℕ) : ℝ) ≤ (N : ℝ) :=
    (Real.sqrt_le_iff).2 ⟨hN0.le, hprodN⟩
  have hlog : Real.log ((n * m : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    calc
      _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hprod hprodN
      _ = 2 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ 1 + Real.log ((n * m : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (n * m : ℕ) := by exact_mod_cast Nat.mul_pos hn hm
    positivity [Real.log_nonneg this]
  exact (abs_sum_jacobiSym_le_of_odd_not_isSquare (n * m) X
    (Nat.mul_pos hn hm) hodd hns).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
      (by linarith) hlog0 (by positivity))

end PellPaper
