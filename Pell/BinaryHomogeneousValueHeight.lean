import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Evaluation heights of homogeneous integral binary forms

A homogeneous binary form of degree `d` has at most `d+1` supported
monomials. The literal evaluation formula therefore gives a value bound
from coefficient and coordinate bounds, including degree zero, the zero
form, and negative coordinates. The logarithmic companion supplies the
value-height step in the manuscript, equation `e:quantitative-value-height`.
-/

namespace PellPaper

open scoped BigOperators

/-- A homogeneous binary form has at most one supported monomial for each
possible exponent of its first variable. No domain hypothesis is needed. -/
theorem card_support_homogeneous_binary_le
    {R : Type*} [CommSemiring R]
    (K : MvPolynomial (Fin 2) R) (d : ℕ) (hK : K.IsHomogeneous d) :
    K.support.card ≤ d + 1 := by
  classical
  have hcard : K.support.card ≤ (Finset.range (d + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun e : Fin 2 →₀ ℕ => e 0)
    · intro e he
      have hdegree := hK (MvPolynomial.mem_support_iff.mp he)
      have hs : e 0 + e 1 = d := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hdegree
      have helt : e 0 < d + 1 := by omega
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr helt)
    · intro e he f hf hef
      change e 0 = f 0 at hef
      have hedegree := hK (MvPolynomial.mem_support_iff.mp he)
      have hfdegree := hK (MvPolynomial.mem_support_iff.mp hf)
      have he' : e 0 + e 1 = d := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hedegree
      have hf' : f 0 + f 1 = d := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hfdegree
      have hef_one : e 1 = f 1 := by omega
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact hef
      · exact hef_one
  simpa using hcard

/-- Literal integer evaluation of a degree-`d` homogeneous binary form is
bounded by `(d+1)*H*T^d` when every coefficient has absolute value at most
`H` and both coordinates have absolute value at most `T`. The nonnegative
bounds may be zero; no nonzero-form or positive-degree premise is needed. -/
theorem abs_eval_homogeneous_binary_le
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (H T : ℝ)
    (hK : K.IsHomogeneous d) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H)
    (y : Fin 2 → ℤ) (hy : ∀ i, |(y i : ℝ)| ≤ T) :
    |((MvPolynomial.eval y K : ℤ) : ℝ)| ≤ ((d : ℝ) + 1) * H * T ^ d := by
  classical
  rw [MvPolynomial.eval_eq']
  push_cast
  calc
    |∑ e ∈ K.support, ((K.coeff e : ℤ) : ℝ) * ∏ i, (y i : ℝ) ^ e i| ≤
        ∑ e ∈ K.support, |((K.coeff e : ℤ) : ℝ) * ∏ i, (y i : ℝ) ^ e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ K.support, H * T ^ d := by
      apply Finset.sum_le_sum
      intro e he
      have hdegree := hK (MvPolynomial.mem_support_iff.mp he)
      have hs : (∑ i : Fin 2, e i) = d := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hdegree
      rw [abs_mul, Finset.abs_prod]
      simp_rw [abs_pow]
      calc
        |((K.coeff e : ℤ) : ℝ)| * ∏ i, |(y i : ℝ)| ^ e i ≤ H * ∏ i, T ^ e i := by
          apply mul_le_mul (hcoeff e) _ (by positivity) hH
          apply Finset.prod_le_prod
          · intro i _
            positivity
          · intro i _
            exact pow_le_pow_left₀ (abs_nonneg _) (hy i) _
        _ = H * T ^ d := by rw [Finset.prod_pow_eq_pow_sum, hs]
    _ = (K.support.card : ℝ) * (H * T ^ d) := by simp
    _ ≤ ((d : ℝ) + 1) * H * T ^ d := by
      have hcard : (K.support.card : ℝ) ≤ (d : ℝ) + 1 := by
        exact_mod_cast card_support_homogeneous_binary_le K d hK
      calc
        _ ≤ ((d : ℝ) + 1) * (H * T ^ d) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hH (pow_nonneg hT d))
        _ = _ := by ring

/-- An explicit logarithmic value-height bound. The additive two makes
the logarithm positive even at zero values. Heights and coordinate bounds
at least one suffice, including constant and zero forms. -/
theorem log_two_add_abs_eval_homogeneous_binary_le
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (H T : ℝ)
    (hK : K.IsHomogeneous d) (hH : 1 ≤ H) (hT : 1 ≤ T)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H)
    (y : Fin 2 → ℤ) (hy : ∀ i, |(y i : ℝ)| ≤ T) :
    Real.log (2 + |((MvPolynomial.eval y K : ℤ) : ℝ)|) ≤
      Real.log 3 + Real.log ((d : ℝ) + 1) + Real.log H + (d : ℝ) * Real.log T := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hd : 1 ≤ (d : ℝ) + 1 := by have hd0 := Nat.cast_nonneg (α := ℝ) d; linarith
  have hA : 1 ≤ ((d : ℝ) + 1) * H * T ^ d :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hd hH) (one_le_pow₀ hT)
  have hvalue := abs_eval_homogeneous_binary_le K d H T hK hHpos.le hTpos.le hcoeff y hy
  have hbound : 2 + |((MvPolynomial.eval y K : ℤ) : ℝ)| ≤
      3 * (((d : ℝ) + 1) * H * T ^ d) := by linarith
  calc
    Real.log (2 + |((MvPolynomial.eval y K : ℤ) : ℝ)|) ≤
        Real.log (3 * (((d : ℝ) + 1) * H * T ^ d)) :=
      Real.log_le_log (by positivity) hbound
    _ = Real.log 3 + Real.log ((d : ℝ) + 1) + Real.log H + (d : ℝ) * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) hHpos.ne', Real.log_pow]
      ring

end PellPaper
