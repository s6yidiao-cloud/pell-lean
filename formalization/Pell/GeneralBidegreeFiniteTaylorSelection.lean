import Pell.GeneralBidegreeSelectedRealWeightedFiltration
import Pell.RectangularInjectionDeterminantExpansion

/-!
# Finite rectangular Taylor selection on the sheared grid

For a finite Taylor factorization, the coefficient factor has columns given by
the ordinary monomials `(a + 2b)^i b^j` on the sheared grid.  The arbitrary
ordered-injection determinant expansion selects a nonzero coefficient minor
directly from a nonzero finite product determinant.  Combining that selection
with the real weighted filtration yields a finite version of the manuscript's
"every nonzero coefficient minor has large total weight" step.

This module is intentionally finite.  Relating the actual exponential matrix
to arbitrarily long finite truncations, and bounding their tails, remains the
analytic Cauchy--Binet gap.
-/

namespace PellPaper

open scoped BigOperators

universe u

/-- The rectangular coefficient matrix whose columns are the selected
ordinary monomial evaluation vectors on `Γ_(A,B)`. -/
noncomputable def generalBidegreeRectangularCoefficientMatrix
    {κ : Type u} (A B : ℕ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix (generalBidegreeGrid A B) κ ℚ :=
  fun p q => generalBidegreeSelectedCoefficientEvaluation A B s q p

/-- The same coefficient matrix over the real field used by finite Taylor
coefficient matrices. -/
noncomputable def generalBidegreeRectangularCoefficientMatrixReal
    {κ : Type u} (A B : ℕ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix (generalBidegreeGrid A B) κ ℝ :=
  (generalBidegreeRectangularCoefficientMatrix A B s).map (algebraMap ℚ ℝ)

/-- The row-dependent two-variable Taylor coefficient at one exponent pair.
It is the literal `α^i β^j / (i! j!)` coefficient from the sheared
exponential expansion. -/
noncomputable def generalBidegreeTaylorCoefficient
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) : ℝ :=
  α r ^ (m 0) * β r ^ (m 1) /
    (Nat.factorial (m 0) : ℝ) / (Nat.factorial (m 1) : ℝ)

/-- The rectangular matrix of finite Taylor coefficients, with a finite
enumeration of exponent pairs as its row index. -/
noncomputable def generalBidegreeFiniteTaylorCoefficientMatrix
    {κ : Type u} (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix κ (generalBidegreeGrid A B) ℝ :=
  fun q r => generalBidegreeTaylorCoefficient A B α β (s q) r

/-- The square finite Taylor evaluation matrix, expanded through a supplied
finite exponent enumeration. -/
noncomputable def generalBidegreeFiniteTaylorEvaluationMatrix
    {κ : Type u} [Fintype κ] (A B : ℕ)
    (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℝ :=
  fun r p => ∑ q,
    generalBidegreeTaylorCoefficient A B α β (s q) r *
      generalBidegreeRectangularCoefficientMatrixReal A B s p q

/-- The finite Taylor matrix factors as the transpose of the product of its
coefficient-evaluation matrix and its Taylor-coefficient matrix. -/
theorem generalBidegreeFiniteTaylorEvaluationMatrix_eq_transpose_mul
    {κ : Type u} [Fintype κ] (A B : ℕ)
    (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeFiniteTaylorEvaluationMatrix A B α β s =
      ((generalBidegreeRectangularCoefficientMatrixReal A B s) *
        (generalBidegreeFiniteTaylorCoefficientMatrix A B α β s)).transpose := by
  ext r p
  simp only [generalBidegreeFiniteTaylorEvaluationMatrix,
    generalBidegreeRectangularCoefficientMatrixReal,
    generalBidegreeFiniteTaylorCoefficientMatrix, Matrix.transpose_apply,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- A nonzero finite rectangular product selects a nonzero rational
coefficient minor.  The product's second factor may be any real finite Taylor
coefficient matrix; its detailed formula is irrelevant to this algebraic
selection step. -/
theorem exists_injective_selectedCoefficientMinor_of_det_mul_ne_zero
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (s : κ → generalBidegreeCoefficientMonomialIndex)
    (T : Matrix κ (generalBidegreeGrid A B) ℝ)
    (hdet : ((generalBidegreeRectangularCoefficientMatrixReal A B s) * T).det ≠ 0) :
    ∃ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
      (generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p.1)).det ≠ 0 := by
  classical
  rcases exists_injective_rectangular_term_of_det_mul_ne_zero
    (generalBidegreeRectangularCoefficientMatrixReal A B s) T hdet with
      ⟨p, hminor, _⟩
  refine ⟨p, ?_⟩
  intro hzero
  apply hminor
  change (((generalBidegreeRectangularCoefficientMatrix A B s).map
    (algebraMap ℚ ℝ)).submatrix id p.1).det = 0
  have hmatrix :
      (generalBidegreeRectangularCoefficientMatrix A B s).submatrix id p.1 =
        generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p.1) := by
    rfl
  change (((algebraMap ℚ ℝ).mapMatrix
    ((generalBidegreeRectangularCoefficientMatrix A B s).submatrix id p.1)).det) = 0
  rw [← (algebraMap ℚ ℝ).map_det, hmatrix, hzero, map_zero]

/-- A nonzero literal finite Taylor determinant selects a nonzero rational
coefficient minor. -/
theorem exists_injective_selectedCoefficientMinor_of_det_finiteTaylor_ne_zero
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (hdet : (generalBidegreeFiniteTaylorEvaluationMatrix A B α β s).det ≠ 0) :
    ∃ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
      (generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p.1)).det ≠ 0 := by
  apply exists_injective_selectedCoefficientMinor_of_det_mul_ne_zero
    A B s (generalBidegreeFiniteTaylorCoefficientMatrix A B α β s)
  intro hzero
  apply hdet
  rw [generalBidegreeFiniteTaylorEvaluationMatrix_eq_transpose_mul,
    Matrix.det_transpose, hzero]

/-- **Finite Taylor selection plus greedy weight.**  From a nonzero finite
rectangular coefficient product, choose an injective Taylor support whose
total real logarithmic weight obeys the exact mesh-scaled parallel-line rank
deficit lower bound. -/
theorem exists_injective_selectedWeightBound_of_det_mul_ne_zero
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (s : κ → generalBidegreeCoefficientMonomialIndex)
    (weight : κ → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ q, weight q = generalBidegreeRealWeight ellM ellX (s q))
    (T : Matrix κ (generalBidegreeGrid A B) ℝ)
    (hdet : ((generalBidegreeRectangularCoefficientMatrixReal A B s) * T).det ≠ 0)
    (hmesh : 0 < mesh) (Q : ℕ) :
    ∃ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
      (∑ n ∈ Finset.range Q,
        ((Fintype.card (generalBidegreeGrid A B) -
          generalBidegreePositiveRealWeightedParallelLineRankCap
            A ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℕ) : ℝ)) * mesh ≤
        ∑ i, weight (p.1 i) := by
  rcases exists_injective_selectedCoefficientMinor_of_det_mul_ne_zero
    A B s T hdet with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledParallelLineDeficits_of_det_ne_zero
    A B (s ∘ p.1) (weight ∘ p.1) ellM ellX mesh hellM_pos hell ?_ hp hmesh Q
  intro i
  exact hweight (p.1 i)

/-- The literal finite Taylor determinant version of the selected greedy
weight bound. -/
theorem exists_injective_selectedWeightBound_of_det_finiteTaylor_ne_zero
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (weight : κ → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ q, weight q = generalBidegreeRealWeight ellM ellX (s q))
    (hdet : (generalBidegreeFiniteTaylorEvaluationMatrix A B α β s).det ≠ 0)
    (hmesh : 0 < mesh) (Q : ℕ) :
    ∃ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
      (∑ n ∈ Finset.range Q,
        ((Fintype.card (generalBidegreeGrid A B) -
          generalBidegreePositiveRealWeightedParallelLineRankCap
            A ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℕ) : ℝ)) * mesh ≤
        ∑ i, weight (p.1 i) := by
  rcases exists_injective_selectedCoefficientMinor_of_det_finiteTaylor_ne_zero
    A B α β s hdet with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledParallelLineDeficits_of_det_ne_zero
    A B (s ∘ p.1) (weight ∘ p.1) ellM ellX mesh hellM_pos hell ?_ hp hmesh Q
  intro i
  exact hweight (p.1 i)

end PellPaper
