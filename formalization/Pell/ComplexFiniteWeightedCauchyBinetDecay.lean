import Pell.FiniteWeightedCauchyBinetDecay

/-!
# Complex finite weighted Cauchy--Binet decay

This module is the complex-norm analogue of the finite weighted determinant
package used by the real sheared fan argument.  It keeps every analytic
scale real and nonnegative while allowing both rectangular matrix factors to
have complex entries.  The result is deliberately finite and does not assert
Taylor convergence, angular localization, or the project-specific weight
lower bound.
-/

namespace PellPaper

open scoped BigOperators

/-- A row-weighted Leibniz bound for a complex square matrix. -/
theorem norm_det_complex_le_factorial_mul_prod_rowBounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (K : ι → ℝ)
    (hbound : ∀ i j, ‖A i j‖ ≤ K i) :
    ‖A.det‖ ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, K i := by
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm ι, ((σ.sign : ℤ) : ℂ) * ∏ i, A (σ i) i‖ ≤
        ∑ σ : Equiv.Perm ι,
          ‖((σ.sign : ℤ) : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [norm_mul, norm_prod, Complex.norm_intCast, ← Int.cast_abs,
        Equiv.Perm.sign_abs, Int.cast_one, one_mul]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, K (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      intro i _
      exact hbound (σ i) i
    _ = ∑ σ : Equiv.Perm ι, ∏ i, K i := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Function.Bijective.prod_comp σ.bijective K
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * ∏ i, K i := by
      simp [nsmul_eq_mul]
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, K i := by
      rw [Fintype.card_perm]

/-- The column version of the complex row-weighted determinant bound. -/
theorem norm_det_complex_submatrix_le_factorial_mul_prod_colBounds
    {n m : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n m ℂ) (p : n → m) (C : m → ℝ)
    (hbound : ∀ i j, ‖U i j‖ ≤ C j) :
    ‖(U.submatrix id p).det‖ ≤
      (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p i) := by
  rw [← Matrix.det_transpose]
  apply norm_det_complex_le_factorial_mul_prod_rowBounds
    (U.submatrix id p).transpose (fun i => C (p i))
  intro i j
  change ‖U j (p i)‖ ≤ C (p i)
  exact hbound j (p i)

/-- Finite weighted Cauchy--Binet decay for complex matrices.  The
coefficient and Taylor scales remain real; the conclusion bounds the complex
norm of the determinant. -/
theorem norm_det_complex_mul_le_factorial_mul_exp_neg_minWeight_mul_sum_pow
    {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (U : Matrix n m ℂ) (V : Matrix m n ℂ)
    (C A weight : m → ℝ) (W : ℝ)
    (hC_nonneg : ∀ q, 0 ≤ C q) (hA_nonneg : ∀ q, 0 ≤ A q)
    (hU : ∀ i q, ‖U i q‖ ≤ C q)
    (hV : ∀ q i, ‖V q i‖ ≤ A q * Real.exp (-weight q))
    (hweight : ∀ p : {p : n → m // Function.Injective p},
      (U.submatrix id p.1).det ≠ 0 → W ≤ ∑ i, weight (p.1 i)) :
    ‖(U * V).det‖ ≤
      (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
        (∑ q, C q * A q) ^ Fintype.card n := by
  rw [det_mul_rectangular_eq_sum_injective]
  calc
    ‖∑ p : {p : n → m // Function.Injective p},
        (U.submatrix id p.1).det * ∏ i, V (p.1 i) i‖ ≤
        ∑ p : {p : n → m // Function.Injective p},
          ‖(U.submatrix id p.1).det * ∏ i, V (p.1 i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p : {p : n → m // Function.Injective p},
        (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
          ∏ i, C (p.1 i) * A (p.1 i) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hpzero : (U.submatrix id p.1).det = 0
      · rw [hpzero, zero_mul, norm_zero]
        have hprodCA_nonneg : 0 ≤ ∏ i, C (p.1 i) * A (p.1 i) :=
          Finset.prod_nonneg fun i _ => mul_nonneg (hC_nonneg _) (hA_nonneg _)
        exact mul_nonneg
          (mul_nonneg (by positivity) (Real.exp_pos _).le) hprodCA_nonneg
      · have hdetbound : ‖(U.submatrix id p.1).det‖ ≤
            (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p.1 i) :=
          norm_det_complex_submatrix_le_factorial_mul_prod_colBounds U p.1 C hU
        have hCprod_nonneg : 0 ≤ ∏ i, C (p.1 i) :=
          Finset.prod_nonneg fun i _ => hC_nonneg _
        have hdetbound_nonneg : 0 ≤
            (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p.1 i) :=
          mul_nonneg (by positivity) hCprod_nonneg
        have hVprod_nonneg : 0 ≤ ∏ i, ‖V (p.1 i) i‖ :=
          Finset.prod_nonneg fun i _ => norm_nonneg _
        have hVprod : (∏ i, ‖V (p.1 i) i‖) ≤
            ∏ i, A (p.1 i) * Real.exp (-weight (p.1 i)) := by
          apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          intro i _
          exact hV (p.1 i) i
        have hprodCA_nonneg : 0 ≤ ∏ i, C (p.1 i) * A (p.1 i) :=
          Finset.prod_nonneg fun i _ => mul_nonneg (hC_nonneg _) (hA_nonneg _)
        calc
          ‖(U.submatrix id p.1).det * ∏ i, V (p.1 i) i‖ =
              ‖(U.submatrix id p.1).det‖ * ∏ i, ‖V (p.1 i) i‖ := by
                rw [norm_mul, norm_prod]
          _ ≤ ((Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p.1 i)) *
              ∏ i, A (p.1 i) * Real.exp (-weight (p.1 i)) := by
                exact mul_le_mul hdetbound hVprod hVprod_nonneg hdetbound_nonneg
          _ = (Nat.factorial (Fintype.card n) : ℝ) *
              ((∏ i, C (p.1 i)) *
                ∏ i, A (p.1 i) * Real.exp (-weight (p.1 i))) := by
                ring
          _ = (Nat.factorial (Fintype.card n) : ℝ) *
              ((∏ i, C (p.1 i) * A (p.1 i)) *
                Real.exp (- ∑ i, weight (p.1 i))) := by
                rw [prod_col_mul_taylorScale_eq_prod_col_mul_exp_neg_sum]
          _ ≤ (Nat.factorial (Fintype.card n) : ℝ) *
              ((∏ i, C (p.1 i) * A (p.1 i)) * Real.exp (-W)) := by
                apply mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (Real.exp_le_exp.mpr (neg_le_neg (hweight p hpzero)))
                    hprodCA_nonneg)
                  (by positivity)
          _ = (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
              ∏ i, C (p.1 i) * A (p.1 i) := by ring
    _ = (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
        ∑ p : {p : n → m // Function.Injective p},
          ∏ i, C (p.1 i) * A (p.1 i) := by
      rw [Finset.mul_sum]
    _ ≤ (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
        ∑ p : n → m, ∏ i, C (p i) * A (p i) := by
      apply mul_le_mul_of_nonneg_left
        (sum_injective_prod_le_sum_all_functions (fun q => C q * A q)
          (fun q => mul_nonneg (hC_nonneg q) (hA_nonneg q)))
      exact mul_nonneg (by positivity) (Real.exp_pos _).le
    _ = (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
        (∑ q, C q * A q) ^ Fintype.card n := by
      rw [sum_all_functions_prod_eq_sum_pow (n := n) (m := m)
        (fun q => C q * A q)]

end PellPaper
