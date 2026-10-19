import Pell.GeneralBidegreeComplexFiniteTaylorCauchyBinetDecay
import Pell.GeneralBidegreeRectangularTaylorFactorization
import Pell.FiniteDeterminantConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Complex analytic limit of rectangular Taylor truncations

This module is the complex analogue of `GeneralBidegreeTaylorLimit`.  It
identifies the rectangular finite Taylor matrices from the complex
Cauchy--Binet module with literal rectangular exponential partial sums, and
then passes entrywise and through the determinant to the limiting complex
sheared-exponential evaluation matrix.

Everything here is an exact identity or a standard convergence consequence.
No local logarithm construction, quantitative determinant estimate,
Pell-cell alignment, integral-minor vanishing, or point count is asserted.
-/

namespace PellPaper

open scoped BigOperators Topology

/-- The degree-`N-1` Taylor approximation to the complex exponential. -/
noncomputable def complexPartialExp (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, z ^ n / (Nat.factorial n : ℂ)

/-- The finite complex Taylor sums converge to the complex exponential. -/
theorem tendsto_complexPartialExp (z : ℂ) :
    Filter.Tendsto (complexPartialExp z) Filter.atTop
      (nhds (Complex.exp z)) := by
  rw [Complex.exp_eq_exp_ℂ]
  change Filter.Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (Nat.factorial n : ℂ))
    Filter.atTop (nhds (NormedSpace.exp z))
  exact (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat

/-- The rectangular two-variable complex Taylor sum through degrees `< N`
in both variables. -/
noncomputable def complexRectangularPartialExp (x y : ℂ) (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    (x ^ i / (Nat.factorial i : ℂ)) *
      (y ^ j / (Nat.factorial j : ℂ))

/-- A rectangular complex Taylor sum separates into two one-variable
partial exponential sums. -/
theorem complexRectangularPartialExp_eq_mul_complexPartialExp
    (x y : ℂ) (N : ℕ) :
    complexRectangularPartialExp x y N =
      complexPartialExp x N * complexPartialExp y N := by
  simp only [complexRectangularPartialExp, complexPartialExp,
    Finset.sum_mul_sum]

/-- Rectangular complex Taylor sums converge to the product of their two
exponential limits. -/
theorem tendsto_complexRectangularPartialExp (x y : ℂ) :
    Filter.Tendsto (complexRectangularPartialExp x y) Filter.atTop
      (nhds (Complex.exp x * Complex.exp y)) := by
  rw [show complexRectangularPartialExp x y =
      fun N => complexPartialExp x N * complexPartialExp y N by
    funext N
    exact complexRectangularPartialExp_eq_mul_complexPartialExp x y N]
  exact (tendsto_complexPartialExp x).mul (tendsto_complexPartialExp y)

/-- The rectangular complex Taylor truncation at one row/column pair of the
sheared coefficient grid. -/
noncomputable def generalBidegreeRectangularTaylorEvaluationMatrixComplex
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ) (N : ℕ) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℂ :=
  fun r p => complexRectangularPartialExp
    (α r * (p.1.1 : ℂ)) (β r * (p.1.2 : ℂ)) N

/-- The limiting complex exponential evaluation matrix corresponding to the
rectangular Taylor truncations. -/
noncomputable def generalBidegreeExponentialEvaluationMatrixComplex
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℂ :=
  fun r p => Complex.exp (α r * (p.1.1 : ℂ)) *
    Complex.exp (β r * (p.1.2 : ℂ))

/-- The same limiting complex matrix in literal sheared-exponential form. -/
noncomputable def generalBidegreeShearedExponentialEvaluationMatrixComplex
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℂ :=
  fun r p => Complex.exp
    ((p.1.1 : ℂ) * α r + (p.1.2 : ℂ) * β r)

/-- The product exponential limit is exactly the complex sheared-column
exponential. -/
theorem generalBidegreeExponentialEvaluationMatrixComplex_eq_sheared
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    generalBidegreeExponentialEvaluationMatrixComplex A B α β =
      generalBidegreeShearedExponentialEvaluationMatrixComplex A B α β := by
  ext r p
  simp only [generalBidegreeExponentialEvaluationMatrixComplex,
    generalBidegreeShearedExponentialEvaluationMatrixComplex]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Entrywise, the rectangular complex Taylor evaluation matrices converge
to the complex exponential evaluation matrix. -/
theorem tendsto_generalBidegreeRectangularTaylorEvaluationMatrixComplex
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    Filter.Tendsto
      (generalBidegreeRectangularTaylorEvaluationMatrixComplex A B α β)
      Filter.atTop
      (nhds (generalBidegreeExponentialEvaluationMatrixComplex A B α β)) := by
  apply tendsto_matrix_of_tendsto_entries
  intro r p
  exact tendsto_complexRectangularPartialExp
    (α r * (p.1.1 : ℂ)) (β r * (p.1.2 : ℂ))

/-- The determinants of the rectangular complex Taylor matrices converge to
the determinant of the limiting complex exponential evaluation matrix. -/
theorem tendsto_det_generalBidegreeRectangularTaylorEvaluationMatrixComplex
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    Filter.Tendsto
      (fun N =>
        (generalBidegreeRectangularTaylorEvaluationMatrixComplex
          A B α β N).det)
      Filter.atTop
      (nhds ((generalBidegreeExponentialEvaluationMatrixComplex
        A B α β).det)) := by
  apply tendsto_det_of_tendsto_matrix
  exact tendsto_generalBidegreeRectangularTaylorEvaluationMatrixComplex A B α β

/-- A nonzero limiting complex exponential determinant persists along every
sufficiently long rectangular Taylor truncation. -/
theorem exists_tail_det_ne_zero_generalBidegreeRectangularTaylorEvaluationMatrixComplex
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ)
    (hdet :
      (generalBidegreeExponentialEvaluationMatrixComplex A B α β).det ≠ 0) :
    ∃ N : ℕ, ∀ k ≥ N,
      (generalBidegreeRectangularTaylorEvaluationMatrixComplex
        A B α β k).det ≠ 0 := by
  apply exists_tail_det_ne_zero_of_tendsto_entries_atTop
    (generalBidegreeRectangularTaylorEvaluationMatrixComplex A B α β)
    (generalBidegreeExponentialEvaluationMatrixComplex A B α β)
  · intro r p
    exact tendsto_complexRectangularPartialExp
      (α r * (p.1.1 : ℂ)) (β r * (p.1.2 : ℂ))
  · exact hdet

/-- On the rectangular Taylor support, the complex coefficient matrix is
the literal complex monomial-evaluation matrix in the two grid coordinates. -/
theorem generalBidegreeRectangularCoefficientMatrixComplex_rectangularTaylorSupport_apply
    (A B N : ℕ) (p : generalBidegreeGrid A B) (ij : Fin N × Fin N) :
    generalBidegreeRectangularCoefficientMatrixComplex A B
      (generalBidegreeRectangularTaylorSupport N) p ij =
      (p.1.1 : ℂ) ^ ij.1.1 * (p.1.2 : ℂ) ^ ij.2.1 := by
  change (algebraMap ℚ ℂ)
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

/-- The literal rectangular complex Taylor truncation is exactly the finite
complex Taylor evaluation matrix for the rectangular support enumeration. -/
theorem generalBidegreeFiniteTaylorEvaluationMatrixComplex_rectangularTaylorSupport
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    generalBidegreeFiniteTaylorEvaluationMatrixComplex A B α β
      (generalBidegreeRectangularTaylorSupport N) =
      generalBidegreeRectangularTaylorEvaluationMatrixComplex A B α β N := by
  ext r p
  simp only [generalBidegreeFiniteTaylorEvaluationMatrixComplex,
    generalBidegreeRectangularTaylorEvaluationMatrixComplex]
  simp_rw [generalBidegreeRectangularCoefficientMatrixComplex_rectangularTaylorSupport_apply]
  simp only [generalBidegreeComplexTaylorCoefficient,
    generalBidegreeRectangularTaylorSupport_zero,
    generalBidegreeRectangularTaylorSupport_one]
  rw [show (∑ q : Fin N × Fin N,
      (α r ^ q.1.1 * β r ^ q.2.1 /
        ↑(Nat.factorial q.1.1) / ↑(Nat.factorial q.2.1)) *
        ((p.1.1 : ℂ) ^ q.1.1 * (p.1.2 : ℂ) ^ q.2.1)) =
      ∑ q : Fin N × Fin N,
        ((α r * (p.1.1 : ℂ)) ^ q.1.1 / ↑(Nat.factorial q.1.1)) *
        ((β r * (p.1.2 : ℂ)) ^ q.2.1 / ↑(Nat.factorial q.2.1)) by
      apply Finset.sum_congr rfl
      intro q _
      rw [mul_pow, mul_pow]
      ring]
  calc
    (∑ q : Fin N × Fin N,
      ((α r * (p.1.1 : ℂ)) ^ q.1.1 / ↑(Nat.factorial q.1.1)) *
        ((β r * (p.1.2 : ℂ)) ^ q.2.1 / ↑(Nat.factorial q.2.1))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((α r * (p.1.1 : ℂ)) ^ i / ↑(Nat.factorial i)) *
          ((β r * (p.1.2 : ℂ)) ^ j / ↑(Nat.factorial j)) :=
        sum_finProduct_eq_sum_range (R := ℂ) N (fun i j =>
          ((α r * (p.1.1 : ℂ)) ^ i / (Nat.factorial i : ℂ)) *
            ((β r * (p.1.2 : ℂ)) ^ j / (Nat.factorial j : ℂ)))
    _ = complexRectangularPartialExp
      (α r * (p.1.1 : ℂ)) (β r * (p.1.2 : ℂ)) N := rfl

/-- The rectangular complex Taylor truncation has the exact finite matrix
factorization supplied by the complex finite Taylor module. -/
theorem generalBidegreeRectangularTaylorEvaluationMatrixComplex_eq_transpose_mul
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℂ) :
    generalBidegreeRectangularTaylorEvaluationMatrixComplex A B α β N =
      ((generalBidegreeRectangularCoefficientMatrixComplex A B
        (generalBidegreeRectangularTaylorSupport N)) *
        (generalBidegreeFiniteTaylorCoefficientMatrixComplex A B α β
          (generalBidegreeRectangularTaylorSupport N))).transpose := by
  rw [← generalBidegreeFiniteTaylorEvaluationMatrixComplex_rectangularTaylorSupport]
  exact generalBidegreeFiniteTaylorEvaluationMatrixComplex_eq_transpose_mul
    A B α β (generalBidegreeRectangularTaylorSupport N)

end PellPaper
