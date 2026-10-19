import Pell.GeneralBidegreeTaylorLimit

/-!
# Exact finite factorization of rectangular Taylor truncations

The analytic module `GeneralBidegreeTaylorLimit` defines a rectangular Taylor
truncation directly as a pair of finite `range` sums.  The finite-selection
module instead accepts an arbitrary finite enumeration of bivariate exponents.
This file identifies the two definitions for the literal rectangular support
`{0, ..., N - 1} × {0, ..., N - 1}`.  Consequently, a nonzero determinant of
the analytic truncation feeds directly into the existing finite coefficient
minor-selection theorem.

This is an exact finite identity; it does not assert nonvanishing of either
the limiting exponential determinant or any Taylor truncation.
-/

namespace PellPaper

open scoped BigOperators

/-- Enumerate the rectangular bivariate Taylor support with both coordinates
strictly below `N`. -/
noncomputable def generalBidegreeRectangularTaylorSupport (N : ℕ) :
    Fin N × Fin N → generalBidegreeCoefficientMonomialIndex :=
  fun ij =>
    Finsupp.single (0 : Fin 2) ij.1.1 + Finsupp.single (1 : Fin 2) ij.2.1

@[simp]
theorem generalBidegreeRectangularTaylorSupport_zero
    (N : ℕ) (ij : Fin N × Fin N) :
    generalBidegreeRectangularTaylorSupport N ij 0 = ij.1.1 := by
  simp [generalBidegreeRectangularTaylorSupport]

@[simp]
theorem generalBidegreeRectangularTaylorSupport_one
    (N : ℕ) (ij : Fin N × Fin N) :
    generalBidegreeRectangularTaylorSupport N ij 1 = ij.2.1 := by
  simp [generalBidegreeRectangularTaylorSupport]

/-- On the rectangular Taylor support, the finite coefficient matrix is the
literal monomial-evaluation matrix in the two grid coordinates. -/
theorem generalBidegreeRectangularCoefficientMatrixReal_rectangularTaylorSupport_apply
    (A B N : ℕ) (p : generalBidegreeGrid A B) (ij : Fin N × Fin N) :
    generalBidegreeRectangularCoefficientMatrixReal A B
      (generalBidegreeRectangularTaylorSupport N) p ij =
      (p.1.1 : ℝ) ^ ij.1.1 * (p.1.2 : ℝ) ^ ij.2.1 := by
  change (algebraMap ℚ ℝ)
    (MvPolynomial.eval (Fin.cases (p.1.1 : ℚ) (fun _ => (p.1.2 : ℚ)))
      (MvPolynomial.monomial (Finsupp.single (0 : Fin 2) ij.1.1 +
        Finsupp.single (1 : Fin 2) ij.2.1) 1)) = _
  rw [MvPolynomial.eval_monomial]
  simp only [one_mul]
  rw [Finsupp.prod_add_index'
    (fun a => by simp)
    (fun a x y => by rw [pow_add])]
  rw [Finsupp.prod_single_index (by simp),
    Finsupp.prod_single_index (by simp)]
  have hindex : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
  rw [hindex, Fin.cases_succ]
  simp

/-- Reindex a rectangular sum over bounded natural numbers by the product of
the two corresponding finite types. -/
theorem sum_finProduct_eq_sum_range {R : Type} [AddCommMonoid R]
    (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ q : Fin N × Fin N, f q.1.1 q.2.1) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j := by
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range N, f i j) N]
  simp_rw [← Fin.sum_univ_eq_sum_range (fun j => f _ j) N]

/-- The source-specific rectangular Taylor truncation is exactly the existing
finite Taylor evaluation matrix for the rectangular support enumeration. -/
theorem generalBidegreeFiniteTaylorEvaluationMatrix_rectangularTaylorSupport
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    generalBidegreeFiniteTaylorEvaluationMatrix A B α β
      (generalBidegreeRectangularTaylorSupport N) =
      generalBidegreeRectangularTaylorEvaluationMatrix A B α β N := by
  ext r p
  simp only [generalBidegreeFiniteTaylorEvaluationMatrix,
    generalBidegreeRectangularTaylorEvaluationMatrix]
  simp_rw [generalBidegreeRectangularCoefficientMatrixReal_rectangularTaylorSupport_apply]
  simp only [generalBidegreeTaylorCoefficient,
    generalBidegreeRectangularTaylorSupport_zero,
    generalBidegreeRectangularTaylorSupport_one]
  rw [show (∑ q : Fin N × Fin N,
      (α r ^ q.1.1 * β r ^ q.2.1 /
        ↑(Nat.factorial q.1.1) / ↑(Nat.factorial q.2.1)) *
        ((p.1.1 : ℝ) ^ q.1.1 * (p.1.2 : ℝ) ^ q.2.1)) =
      ∑ q : Fin N × Fin N,
        ((α r * (p.1.1 : ℝ)) ^ q.1.1 / ↑(Nat.factorial q.1.1)) *
        ((β r * (p.1.2 : ℝ)) ^ q.2.1 / ↑(Nat.factorial q.2.1)) by
      apply Finset.sum_congr rfl
      intro q _
      rw [mul_pow, mul_pow]
      ring]
  calc
    (∑ q : Fin N × Fin N,
      ((α r * (p.1.1 : ℝ)) ^ q.1.1 / ↑(Nat.factorial q.1.1)) *
        ((β r * (p.1.2 : ℝ)) ^ q.2.1 / ↑(Nat.factorial q.2.1))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((α r * (p.1.1 : ℝ)) ^ i / ↑(Nat.factorial i)) *
          ((β r * (p.1.2 : ℝ)) ^ j / ↑(Nat.factorial j)) :=
        sum_finProduct_eq_sum_range N (fun i j =>
          ((α r * (p.1.1 : ℝ)) ^ i / ↑(Nat.factorial i)) *
            ((β r * (p.1.2 : ℝ)) ^ j / ↑(Nat.factorial j)))
    _ = rectangularPartialExp (α r * (p.1.1 : ℝ))
      (β r * (p.1.2 : ℝ)) N := rfl

/-- The rectangular Taylor truncation has the same explicit finite matrix
factorization as the general finite Taylor evaluation matrix. -/
theorem generalBidegreeRectangularTaylorEvaluationMatrix_eq_transpose_mul
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    generalBidegreeRectangularTaylorEvaluationMatrix A B α β N =
      ((generalBidegreeRectangularCoefficientMatrixReal A B
        (generalBidegreeRectangularTaylorSupport N)) *
        (generalBidegreeFiniteTaylorCoefficientMatrix A B α β
          (generalBidegreeRectangularTaylorSupport N))).transpose := by
  rw [← generalBidegreeFiniteTaylorEvaluationMatrix_rectangularTaylorSupport]
  exact generalBidegreeFiniteTaylorEvaluationMatrix_eq_transpose_mul A B α β
    (generalBidegreeRectangularTaylorSupport N)

/-- A nonzero rectangular Taylor determinant selects a nonzero rational
coefficient minor from its explicitly enumerated rectangular support. -/
theorem exists_injective_selectedCoefficientMinor_of_det_rectangularTaylor_ne_zero
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (hdet :
      (generalBidegreeRectangularTaylorEvaluationMatrix A B α β N).det ≠ 0) :
    ∃ p : {p : generalBidegreeGrid A B → Fin N × Fin N // Function.Injective p},
      (generalBidegreeSelectedCoefficientEvaluationMatrix A B
        (generalBidegreeRectangularTaylorSupport N ∘ p.1)).det ≠ 0 := by
  apply exists_injective_selectedCoefficientMinor_of_det_finiteTaylor_ne_zero
    A B α β (generalBidegreeRectangularTaylorSupport N)
  rw [generalBidegreeFiniteTaylorEvaluationMatrix_rectangularTaylorSupport]
  exact hdet

end PellPaper
