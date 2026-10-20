import Pell.BinaryHomogeneousProductHeight
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Coefficient height under a binary integral linear substitution

This candidate records the elementary height cost of substituting two
integral linear forms into a homogeneous binary polynomial.  For a degree
`d` form of coefficient height `H` and a two-by-two matrix of entry height
`L`, every transformed coefficient is bounded by
`(d + 1) * H * (2 * L) ^ d`.

No determinant or nonvanishing hypothesis is needed.  In particular, the
statement includes zero matrices, zero polynomials, and degree zero.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The linear form given by row `i` of an integral two-by-two matrix. -/
def binaryLinearSubstitutionForm
    (W : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C (W i 0) * MvPolynomial.X 0 +
    MvPolynomial.C (W i 1) * MvPolynomial.X 1

/-- Substitute the two row-linear forms of `W` for the two variables. -/
def binaryLinearSubstitution
    (W : Matrix (Fin 2) (Fin 2) ℤ) :
    MvPolynomial (Fin 2) ℤ →ₐ[ℤ] MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.bind₁ (binaryLinearSubstitutionForm W)

/-- Every row-linear form is homogeneous of degree one, including a zero
row. -/
theorem binaryLinearSubstitutionForm_isHomogeneous
    (W : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    (binaryLinearSubstitutionForm W i).IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_C_mul_X (W i 0) 0).add
    (MvPolynomial.isHomogeneous_C_mul_X (W i 1) 1)

/-- Linear substitution preserves the degree of a homogeneous binary form,
including when the original or transformed polynomial is zero. -/
theorem binaryLinearSubstitution_isHomogeneous
    (W : Matrix (Fin 2) (Fin 2) ℤ)
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hK : K.IsHomogeneous d) :
    (binaryLinearSubstitution W K).IsHomogeneous d := by
  rw [binaryLinearSubstitution, ← MvPolynomial.aeval_eq_bind₁]
  simpa only [one_mul] using
    hK.aeval (binaryLinearSubstitutionForm W)
      (binaryLinearSubstitutionForm_isHomogeneous W)

/-- Multiplication by one row-linear form enlarges a uniform integral
coefficient bound by at most `2 * L`. -/
theorem abs_coeff_binaryLinearSubstitutionForm_mul_le
    (W : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2)
    (Q : MvPolynomial (Fin 2) ℤ) (L HQ : ℤ)
    (hL : 0 ≤ L) (hHQ : 0 ≤ HQ)
    (hW : ∀ r c, |W r c| ≤ L)
    (hQ : ∀ e, |Q.coeff e| ≤ HQ)
    (e : Fin 2 →₀ ℕ) :
    |(binaryLinearSubstitutionForm W i * Q).coeff e| ≤ (2 * L) * HQ := by
  have hzero :
      |((MvPolynomial.C (W i 0) * MvPolynomial.X 0) * Q).coeff e| ≤ L * HQ := by
    rw [mul_assoc, mul_comm (MvPolynomial.X 0) Q,
      MvPolynomial.coeff_C_mul, abs_mul]
    exact mul_le_mul (hW i 0)
      (abs_coeff_mul_X_le Q HQ hHQ hQ 0 e) (abs_nonneg _) hL
  have hone :
      |((MvPolynomial.C (W i 1) * MvPolynomial.X 1) * Q).coeff e| ≤ L * HQ := by
    rw [mul_assoc, mul_comm (MvPolynomial.X 1) Q,
      MvPolynomial.coeff_C_mul, abs_mul]
    exact mul_le_mul (hW i 1)
      (abs_coeff_mul_X_le Q HQ hHQ hQ 1 e) (abs_nonneg _) hL
  rw [binaryLinearSubstitutionForm, add_mul, MvPolynomial.coeff_add]
  calc
    |((MvPolynomial.C (W i 0) * MvPolynomial.X 0) * Q).coeff e +
        ((MvPolynomial.C (W i 1) * MvPolynomial.X 1) * Q).coeff e| ≤
        |((MvPolynomial.C (W i 0) * MvPolynomial.X 0) * Q).coeff e| +
          |((MvPolynomial.C (W i 1) * MvPolynomial.X 1) * Q).coeff e| :=
      abs_add_le _ _
    _ ≤ L * HQ + L * HQ := add_le_add hzero hone
    _ = (2 * L) * HQ := by ring

/-- Iterating one row-linear form gives the exact exponential height cost;
the second factor need not be homogeneous. -/
theorem abs_coeff_binaryLinearSubstitutionForm_pow_mul_le
    (W : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) (a : ℕ)
    (Q : MvPolynomial (Fin 2) ℤ) (L HQ : ℤ)
    (hL : 0 ≤ L) (hHQ : 0 ≤ HQ)
    (hW : ∀ r c, |W r c| ≤ L)
    (hQ : ∀ e, |Q.coeff e| ≤ HQ)
    (e : Fin 2 →₀ ℕ) :
    |((binaryLinearSubstitutionForm W i) ^ a * Q).coeff e| ≤
      (2 * L) ^ a * HQ := by
  induction a generalizing e with
  | zero => simpa using hQ e
  | succ a ha =>
      have hbase : 0 ≤ 2 * L := mul_nonneg (by norm_num) hL
      have hnext : 0 ≤ (2 * L) ^ a * HQ :=
        mul_nonneg (pow_nonneg hbase a) hHQ
      have hstep := abs_coeff_binaryLinearSubstitutionForm_mul_le
        W i ((binaryLinearSubstitutionForm W i) ^ a * Q)
        L ((2 * L) ^ a * HQ) hL hnext hW (fun f => ha f) e
      calc
        |((binaryLinearSubstitutionForm W i) ^ (a + 1) * Q).coeff e| =
            |(binaryLinearSubstitutionForm W i *
              ((binaryLinearSubstitutionForm W i) ^ a * Q)).coeff e| := by
          congr 2
          rw [pow_succ]
          ring
        _ ≤ (2 * L) * ((2 * L) ^ a * HQ) := hstep
        _ = (2 * L) ^ (a + 1) * HQ := by
          rw [pow_succ]
          ring

/-- The substituted monomial part in two variables has coefficient height
at most `(2 * L)` to its total degree. -/
theorem abs_coeff_binaryLinearSubstitutionPowers_le
    (W : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℕ) (L : ℤ)
    (hL : 0 ≤ L) (hW : ∀ r c, |W r c| ≤ L)
    (e : Fin 2 →₀ ℕ) :
    |((binaryLinearSubstitutionForm W 0) ^ a *
        (binaryLinearSubstitutionForm W 1) ^ b).coeff e| ≤
      (2 * L) ^ (a + b) := by
  have hone : ∀ e : Fin 2 →₀ ℕ,
      |((1 : MvPolynomial (Fin 2) ℤ).coeff e)| ≤ 1 := by
    intro f
    rw [MvPolynomial.coeff_one]
    split_ifs <;> norm_num
  have hb : ∀ f : Fin 2 →₀ ℕ,
      |((binaryLinearSubstitutionForm W 1) ^ b).coeff f| ≤ (2 * L) ^ b := by
    intro f
    simpa using
      (abs_coeff_binaryLinearSubstitutionForm_pow_mul_le
        W 1 b (1 : MvPolynomial (Fin 2) ℤ) L 1 hL (by norm_num) hW hone f)
  have hbase : 0 ≤ 2 * L := mul_nonneg (by norm_num) hL
  have hpow : 0 ≤ (2 * L) ^ b := pow_nonneg hbase b
  have hab := abs_coeff_binaryLinearSubstitutionForm_pow_mul_le
    W 0 a ((binaryLinearSubstitutionForm W 1) ^ b) L ((2 * L) ^ b)
    hL hpow hW hb e
  simpa [pow_add] using hab

/-- Main coefficient-height transport theorem.  A homogeneous degree-`d`
binary form with coefficient height `H`, after an arbitrary integral linear
substitution of entry height `L`, has coefficient height at most
`(d + 1) * H * (2 * L) ^ d`. -/
theorem abs_coeff_binaryLinearSubstitution_le
    (W : Matrix (Fin 2) (Fin 2) ℤ)
    (K : MvPolynomial (Fin 2) ℤ) (d : ℕ) (H L : ℤ)
    (hK : K.IsHomogeneous d) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hcoeff : ∀ e, |K.coeff e| ≤ H)
    (hW : ∀ i j, |W i j| ≤ L)
    (e : Fin 2 →₀ ℕ) :
    |(binaryLinearSubstitution W K).coeff e| ≤
      ((d : ℤ) + 1) * H * (2 * L) ^ d := by
  classical
  have hexpand :
      binaryLinearSubstitution W K =
        ∑ s ∈ K.support,
          binaryLinearSubstitution W (MvPolynomial.monomial s (K.coeff s)) := by
    calc
      binaryLinearSubstitution W K =
          binaryLinearSubstitution W
            (∑ s ∈ K.support, MvPolynomial.monomial s (K.coeff s)) := by
        exact congrArg (binaryLinearSubstitution W) K.as_sum
      _ = ∑ s ∈ K.support,
          binaryLinearSubstitution W (MvPolynomial.monomial s (K.coeff s)) := by
        simp only [map_sum]
  rw [hexpand, MvPolynomial.coeff_sum]
  calc
    |∑ s ∈ K.support,
        (binaryLinearSubstitution W (MvPolynomial.monomial s (K.coeff s))).coeff e| ≤
        ∑ s ∈ K.support,
          |(binaryLinearSubstitution W (MvPolynomial.monomial s (K.coeff s))).coeff e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ K.support, H * (2 * L) ^ d := by
      apply Finset.sum_le_sum
      intro s hs
      have hdegree : s 0 + s 1 = d := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using
          hK (MvPolynomial.mem_support_iff.mp hs)
      have hpowers := abs_coeff_binaryLinearSubstitutionPowers_le
        W (s 0) (s 1) L hL hW e
      simp only [binaryLinearSubstitution, MvPolynomial.monomial_fin_two,
        map_mul, map_pow, MvPolynomial.bind₁_C_right,
        MvPolynomial.bind₁_X_right]
      rw [mul_assoc, MvPolynomial.coeff_C_mul, abs_mul]
      calc
        |K.coeff s| *
            |((binaryLinearSubstitutionForm W 0) ^ s 0 *
              (binaryLinearSubstitutionForm W 1) ^ s 1).coeff e| ≤
            H * (2 * L) ^ (s 0 + s 1) :=
          mul_le_mul (hcoeff s) hpowers (abs_nonneg _) hH
        _ = H * (2 * L) ^ d := by rw [hdegree]
    _ = (K.support.card : ℤ) * (H * (2 * L) ^ d) := by simp
    _ ≤ ((d : ℤ) + 1) * (H * (2 * L) ^ d) := by
      have hcard : (K.support.card : ℤ) ≤ (d : ℤ) + 1 := by
        exact_mod_cast card_support_homogeneous_binary_le K d hK
      exact mul_le_mul_of_nonneg_right hcard
        (mul_nonneg hH (pow_nonneg (mul_nonneg (by norm_num) hL) d))
    _ = ((d : ℤ) + 1) * H * (2 * L) ^ d := by ring

end
end PellPaper
