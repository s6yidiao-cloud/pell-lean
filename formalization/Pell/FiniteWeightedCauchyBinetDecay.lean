import Pell.RowWeightedDeterminantBound
import Pell.RectangularInjectionDeterminantExpansion
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A finite weighted Cauchy--Binet decay package

This module isolates the finite estimate behind the analytic determinant
argument.  Columnwise bounds for the coefficient-evaluation matrix and
rowwise exponentially weighted bounds for the Taylor matrix yield a bound
for a finite rectangular product.  A lower bound for the total weight of
every nonzero coefficient minor can then be factored out of the whole
ordered Cauchy--Binet sum.

The result is finite and makes no claim about the uniform convergence of an
infinite Taylor expansion or the sharp lattice-counting lower bound for the
weights.
-/

namespace PellPaper

open scoped BigOperators

/-- The transpose of the row-weighted determinant estimate: if the `j`th
column is bounded by `C j`, then a selected square column minor is bounded by
`n!` times the product of its selected column bounds. -/
theorem abs_det_submatrix_le_factorial_mul_prod_colBounds
    {n m : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n m ℝ) (p : n → m) (C : m → ℝ)
    (hbound : ∀ i j, |U i j| ≤ C j) :
    |(U.submatrix id p).det| ≤
      (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p i) := by
  rw [← Matrix.det_transpose]
  apply abs_det_le_factorial_mul_prod_rowBounds
    (U.submatrix id p).transpose (fun i => C (p i))
  intro i j
  change |U j (p i)| ≤ C (p i)
  exact hbound j (p i)

/-- Summing a product of one-variable factors over every function is the
corresponding power of their total sum. -/
theorem sum_all_functions_prod_eq_sum_pow
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (f : m → ℝ) :
    (∑ p : n → m, ∏ i, f (p i)) =
      (∑ q, f q) ^ Fintype.card n := by
  calc
    (∑ p : n → m, ∏ i, f (p i)) =
        ∑ p ∈ Fintype.piFinset (fun _ : n => (Finset.univ : Finset m)),
          ∏ i, f (p i) := by
            rw [Fintype.piFinset_univ]
    _ = ∏ _ : n, ∑ q : m, f q := by
      rw [Finset.sum_prod_piFinset]
    _ = (∑ q, f q) ^ Fintype.card n := by
      simp [Finset.prod_const]

/-- Restricting the nonnegative product sum to injective choices can only
decrease it. -/
theorem sum_injective_prod_le_sum_all_functions
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (f : m → ℝ) (hf : ∀ q, 0 ≤ f q) :
    (∑ p : {p : n → m // Function.Injective p}, ∏ i, f (p.1 i)) ≤
      ∑ p : n → m, ∏ i, f (p i) := by
  classical
  let g : (n → m) → ℝ := fun p => ∏ i, f (p i)
  change (∑ p : {p : n → m // Function.Injective p}, g p.1) ≤
    ∑ p : n → m, g p
  calc
    (∑ p : {p : n → m // Function.Injective p}, g p.1) ≤
        (∑ p : {p : n → m // Function.Injective p}, g p.1) +
          ∑ p : {p : n → m // ¬ Function.Injective p}, g p.1 := by
            apply le_add_of_nonneg_right
            apply Finset.sum_nonneg
            intro p _
            exact Finset.prod_nonneg fun i _ => hf (p.1 i)
    _ = ∑ p : n → m, g p :=
      Fintype.sum_subtype_add_sum_subtype (fun p : n → m => Function.Injective p) g

/-- Separate the exponential factor from a product of column and Taylor
scales. -/
theorem prod_col_mul_taylorScale_eq_prod_col_mul_exp_neg_sum
    {n m : Type*} [Fintype n]
    (p : n → m) (C A weight : m → ℝ) :
    (∏ i, C (p i)) * (∏ i, A (p i) * Real.exp (-weight (p i))) =
      (∏ i, C (p i) * A (p i)) *
        Real.exp (- ∑ i, weight (p i)) := by
  calc
    (∏ i, C (p i)) * (∏ i, A (p i) * Real.exp (-weight (p i))) =
        ((∏ i, C (p i)) * ∏ i, A (p i)) *
          ∏ i, Real.exp (-weight (p i)) := by
            rw [Finset.prod_mul_distrib]
            ring
    _ = (∏ i, C (p i) * A (p i)) *
          ∏ i, Real.exp (-weight (p i)) := by
            rw [← Finset.prod_mul_distrib]
    _ = (∏ i, C (p i) * A (p i)) *
          Real.exp (- ∑ i, weight (p i)) := by
            rw [← Finset.sum_neg_distrib, Real.exp_sum]

/-- Finite Cauchy--Binet decay after a weighted minor lower bound.  The
coefficient matrix has columnwise scales `C`, the Taylor matrix has rowwise
scales `A q * exp (-weight q)`, and every nonzero coefficient minor has total
weight at least `W`.  The finite support sum is then bounded by the full
product expansion of `∑ q, C q * A q`. -/
theorem abs_det_mul_le_factorial_mul_exp_neg_minWeight_mul_sum_pow
    {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (U : Matrix n m ℝ) (V : Matrix m n ℝ)
    (C A weight : m → ℝ) (W : ℝ)
    (hC_nonneg : ∀ q, 0 ≤ C q) (hA_nonneg : ∀ q, 0 ≤ A q)
    (hU : ∀ i q, |U i q| ≤ C q)
    (hV : ∀ q i, |V q i| ≤ A q * Real.exp (-weight q))
    (hweight : ∀ p : {p : n → m // Function.Injective p},
      (U.submatrix id p.1).det ≠ 0 → W ≤ ∑ i, weight (p.1 i)) :
    |(U * V).det| ≤
      (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
        (∑ q, C q * A q) ^ Fintype.card n := by
  rw [det_mul_rectangular_eq_sum_injective]
  calc
    |∑ p : {p : n → m // Function.Injective p},
        (U.submatrix id p.1).det * ∏ i, V (p.1 i) i| ≤
        ∑ p : {p : n → m // Function.Injective p},
          |(U.submatrix id p.1).det * ∏ i, V (p.1 i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : {p : n → m // Function.Injective p},
        (Nat.factorial (Fintype.card n) : ℝ) * Real.exp (-W) *
          ∏ i, C (p.1 i) * A (p.1 i) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hpzero : (U.submatrix id p.1).det = 0
      · rw [hpzero, zero_mul, abs_zero]
        have hprodCA_nonneg : 0 ≤ ∏ i, C (p.1 i) * A (p.1 i) :=
          Finset.prod_nonneg fun i _ => mul_nonneg (hC_nonneg _) (hA_nonneg _)
        exact mul_nonneg
          (mul_nonneg (by positivity) (Real.exp_pos _).le) hprodCA_nonneg
      · have hdetbound : |(U.submatrix id p.1).det| ≤
            (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p.1 i) :=
          abs_det_submatrix_le_factorial_mul_prod_colBounds U p.1 C hU
        have hCprod_nonneg : 0 ≤ ∏ i, C (p.1 i) :=
          Finset.prod_nonneg fun i _ => hC_nonneg _
        have hdetbound_nonneg : 0 ≤
            (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p.1 i) :=
          mul_nonneg (by positivity) hCprod_nonneg
        have hVprod_nonneg : 0 ≤ ∏ i, |V (p.1 i) i| :=
          Finset.prod_nonneg fun i _ => abs_nonneg _
        have hVprod : (∏ i, |V (p.1 i) i|) ≤
            ∏ i, A (p.1 i) * Real.exp (-weight (p.1 i)) := by
          apply Finset.prod_le_prod
          · intro i _
            exact abs_nonneg _
          intro i _
          exact hV (p.1 i) i
        have hprodCA_nonneg : 0 ≤ ∏ i, C (p.1 i) * A (p.1 i) :=
          Finset.prod_nonneg fun i _ => mul_nonneg (hC_nonneg _) (hA_nonneg _)
        calc
          |(U.submatrix id p.1).det * ∏ i, V (p.1 i) i| =
              |(U.submatrix id p.1).det| * ∏ i, |V (p.1 i) i| := by
                rw [abs_mul, Finset.abs_prod]
          _ ≤ ((Nat.factorial (Fintype.card n) : ℝ) * ∏ i, C (p.1 i)) *
              ∏ i, A (p.1 i) * Real.exp (-weight (p.1 i)) :=
                by exact mul_le_mul hdetbound hVprod hVprod_nonneg hdetbound_nonneg
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
