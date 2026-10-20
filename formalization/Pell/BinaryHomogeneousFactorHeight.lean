import Pell.SquarefreePolynomialLinearNonsquare
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Coefficient heights of integer homogeneous binary factors

Dehomogenization on the chart `(X,1)` preserves the coefficients of a
homogeneous binary form. Mathlib's Mahler-measure factor bound therefore
gives an explicit Gelfond-style bound, with no primitive or squarefree
hypothesis. This supplies the factor-height step for the squarefree part
of the eliminant in the manuscript, Lemma `L:quantitative-eliminant-height`.
-/

namespace PellPaper

open Polynomial

noncomputable section

private theorem binary_dehom_natDegree_le
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hK : K.IsHomogeneous d) :
    (binaryDehomogenizeAtOne K).natDegree ≤ d := by
  refine le_trans ?_ hK.totalDegree_le
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 e).trans (MvPolynomial.le_totalDegree he)

private theorem binary_homogenize_dehom_eq
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hK : K.IsHomogeneous d) :
    (binaryDehomogenizeAtOne K).homogenize d = K := by
  apply Polynomial.homogenize_eq_of_isHomogeneous hK
  rfl

private theorem binary_dehom_ne_zero
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hK : K.IsHomogeneous d) (hK0 : K ≠ 0) :
    binaryDehomogenizeAtOne K ≠ 0 := by
  intro hzero
  apply hK0
  rw [← binary_homogenize_dehom_eq K d hK, hzero, Polynomial.homogenize_zero]

private theorem abs_coeff_binary_dehom_le
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (H : ℝ)
    (hK : K.IsHomogeneous d) (hH : 0 ≤ H)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H) (n : ℕ) :
    |((binaryDehomogenizeAtOne K).coeff n : ℝ)| ≤ H := by
  by_cases hn : n ≤ d
  · have h := hcoeff (Finsupp.single 0 n + Finsupp.single 1 (d - n))
    rw [← binary_homogenize_dehom_eq K d hK, Polynomial.coeff_homogenize] at h
    simpa [Nat.add_sub_of_le hn] using h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((binary_dehom_natDegree_le K d hK).trans_lt (lt_of_not_ge hn))]
    simpa using hH

private theorem one_le_mahlerMeasure_int_map
    (p : Polynomial ℤ) (hp : p ≠ 0) :
    1 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  apply Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  rw [Polynomial.leadingCoeff_map_of_injective (Int.cast_injective)]
  change 1 ≤ ‖(p.leadingCoeff : ℂ)‖
  rw [Complex.norm_intCast]
  have hpos : (0 : ℤ) < |p.leadingCoeff| :=
    abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hbound : (1 : ℤ) ≤ |p.leadingCoeff| := by omega
  exact_mod_cast hbound

private theorem abs_coeff_int_factor_le
    (p q : Polynomial ℤ) (d : ℕ) (H : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hqp : q ∣ p) (hdeg : p.natDegree ≤ d)
    (hH : 0 ≤ H) (hcoeff : ∀ n, |(p.coeff n : ℝ)| ≤ H) (n : ℕ) :
    |(q.coeff n : ℝ)| ≤ (2 : ℝ) ^ d * ((d : ℝ) + 1) * H := by
  classical
  obtain ⟨r, hpr⟩ := hqp
  have hr : r ≠ 0 := by intro h; simp [h] at hpr; exact hp hpr
  let pc : Polynomial ℂ := p.map (Int.castRingHom ℂ)
  let qc : Polynomial ℂ := q.map (Int.castRingHom ℂ)
  let rc : Polynomial ℂ := r.map (Int.castRingHom ℂ)
  have hpc : pc = qc * rc := by simp [pc, qc, rc, hpr]
  have hrc : 1 ≤ rc.mahlerMeasure := one_le_mahlerMeasure_int_map r hr
  have hpcdeg : pc.natDegree ≤ d := by
    dsimp only [pc]
    rw [Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom ℂ) (by exact Int.cast_injective)]
    exact hdeg
  have hqcdeg : qc.natDegree ≤ d := by
    have hqd : q.natDegree ≤ d := by
      have hmul := Polynomial.natDegree_mul hq hr
      rw [← hpr] at hmul
      omega
    dsimp only [qc]
    rw [Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom ℂ) (by exact Int.cast_injective)]
    exact hqd
  have hmass : pc.mahlerMeasure ≤ ((d : ℝ) + 1) * H := by
    apply pc.mahlerMeasure_le_sum_norm_coeff.trans
    rw [Polynomial.sum_def]
    calc
      (∑ i ∈ pc.support, ‖pc.coeff i‖) ≤ ∑ _i ∈ pc.support, H := by
        apply Finset.sum_le_sum
        intro i _
        simpa [pc] using hcoeff i
      _ = (pc.support.card : ℝ) * H := by simp
      _ ≤ ((d : ℝ) + 1) * H := by
        gcongr
        exact_mod_cast pc.card_supp_le_succ_natDegree.trans (Nat.add_le_add_right hpcdeg 1)
  have hchoose : (qc.natDegree.choose n : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      (qc.natDegree.choose n : ℝ) ≤ (2 : ℝ) ^ qc.natDegree := by
        exact_mod_cast Nat.choose_le_two_pow qc.natDegree n
      _ ≤ (2 : ℝ) ^ d := by gcongr; norm_num
  calc
    |(q.coeff n : ℝ)| = ‖qc.coeff n‖ := by simp [qc]
    _ ≤ (qc.natDegree.choose n : ℝ) * pc.mahlerMeasure := by
      rw [hpc]
      exact Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
        n qc rc hrc
    _ ≤ (2 : ℝ) ^ d * (((d : ℝ) + 1) * H) :=
      mul_le_mul hchoose hmass pc.mahlerMeasure_nonneg (by positivity)
    _ = (2 : ℝ) ^ d * ((d : ℝ) + 1) * H := by ring

/-- Every integral homogeneous binary divisor has coefficient height at most
`2^d * (d+1)` times a coefficient bound for the nonzero dividend of degree `d`.
No primitive, squarefree, leading-sign or caller-supplied factor-height
condition is required. -/
theorem abs_coeff_homogeneous_binary_factor_le
    (K J : MvPolynomial (Fin 2) ℤ) (d j : ℕ) (H : ℝ)
    (hK : K.IsHomogeneous d) (hJ : J.IsHomogeneous j)
    (hK0 : K ≠ 0) (hJK : J ∣ K) (hH : 0 ≤ H)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H) (e : Fin 2 →₀ ℕ) :
    |((J.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ d * ((d : ℝ) + 1) * H := by
  have hJ0 : J ≠ 0 := by
    intro hzero
    rw [hzero, zero_dvd_iff] at hJK
    exact hK0 hJK
  have hJdehom0 := binary_dehom_ne_zero J j hJ hJ0
  have hdehomDvd : binaryDehomogenizeAtOne J ∣ binaryDehomogenizeAtOne K :=
    map_dvd (MvPolynomial.eval₂Hom Polynomial.C
      ![Polynomial.X, (1 : Polynomial ℤ)]) hJK
  have hbound := abs_coeff_int_factor_le
    (binaryDehomogenizeAtOne K) (binaryDehomogenizeAtOne J) d H
    (binary_dehom_ne_zero K d hK hK0) hJdehom0 hdehomDvd
    (binary_dehom_natDegree_le K d hK) hH
    (abs_coeff_binary_dehom_le K d H hK hH hcoeff) (e 0)
  rw [← binary_homogenize_dehom_eq J j hJ, Polynomial.coeff_homogenize]
  split_ifs
  · exact hbound
  · simp only [Int.cast_zero, abs_zero]
    positivity

/-- A logarithmic coefficient-height estimate with explicit constants.
The lower bound `H>=1` handles zero coefficients with Lean's total logarithm. -/
theorem log_abs_coeff_homogeneous_binary_factor_le
    (K J : MvPolynomial (Fin 2) ℤ) (d j : ℕ) (H : ℝ)
    (hK : K.IsHomogeneous d) (hJ : J.IsHomogeneous j)
    (hK0 : K ≠ 0) (hJK : J ∣ K) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ H) (e : Fin 2 →₀ ℕ) :
    Real.log |((J.coeff e : ℤ) : ℝ)| ≤
      Real.log H + (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  by_cases he : J.coeff e = 0
  · simp only [he, Int.cast_zero, abs_zero, Real.log_zero]
    exact add_nonneg
      (add_nonneg (Real.log_nonneg hH)
        (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by norm_num))))
      (Real.log_nonneg (by have hd := Nat.cast_nonneg (α := ℝ) d; linarith))
  · have hepos : 0 < |((J.coeff e : ℤ) : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast he)
    have hlog := Real.log_le_log hepos
      (abs_coeff_homogeneous_binary_factor_le K J d j H hK hJ hK0 hJK hHpos.le hcoeff e)
    calc
      Real.log |((J.coeff e : ℤ) : ℝ)| ≤
          Real.log ((2 : ℝ) ^ d * ((d : ℝ) + 1) * H) := hlog
      _ = Real.log H + (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) := by
        rw [Real.log_mul (by positivity) hHpos.ne',
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring

end
end PellPaper
