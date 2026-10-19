import Pell.ComplexFiniteWeightedCauchyBinetDecay
import Pell.GeneralBidegreeFiniteTaylorCauchyBinetDecay

/-!
# Complex finite Taylor Cauchy--Binet decay on the general bidegree grid

This module supplies the finite complex analogue of the existing real
general-bidegree Taylor factorization.  The coefficient matrix is the
literal rational monomial-evaluation matrix cast to `ℂ`; the two Taylor
variables and the resulting finite matrices are complex.  A nonzero complex
coefficient minor is transported back to the same rational minor, so the
existing rational weighted filtration can be used without changing its
notion of rank.

Everything here is finite.  No convergence, local complex logarithm,
project-specific fan estimate, Pell-cell evaluation identity, integral-minor
vanishing, or point count is asserted.
-/

namespace PellPaper

open scoped BigOperators

universe u

/-- The rational ordinary-monomial coefficient matrix, cast entrywise to
the complex field. -/
noncomputable def generalBidegreeRectangularCoefficientMatrixComplex
    {κ : Type u} (A B : ℕ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix (generalBidegreeGrid A B) κ ℂ :=
  (generalBidegreeRectangularCoefficientMatrix A B s).map (algebraMap ℚ ℂ)

/-- Casting the rational coefficient matrix to `ℂ` preserves exactly the
absolute value of its real cast. -/
theorem norm_generalBidegreeRectangularCoefficientMatrixComplex_eq_abs_real
    {κ : Type u} (A B : ℕ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (q : κ) :
    ‖generalBidegreeRectangularCoefficientMatrixComplex A B s r q‖ =
      |generalBidegreeRectangularCoefficientMatrixReal A B s r q| := by
  change ‖((generalBidegreeRectangularCoefficientMatrix A B s r q : ℚ) : ℂ)‖ =
    |((generalBidegreeRectangularCoefficientMatrix A B s r q : ℚ) : ℝ)|
  exact Complex.norm_ratCast _

/-- The literal complex two-variable Taylor coefficient
`alpha^i beta^j / (i! j!)`. -/
noncomputable def generalBidegreeComplexTaylorCoefficient
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) : ℂ :=
  α r ^ (m 0) * β r ^ (m 1) /
    (Nat.factorial (m 0) : ℂ) / (Nat.factorial (m 1) : ℂ)

/-- The finite rectangular matrix of complex Taylor coefficients. -/
noncomputable def generalBidegreeFiniteTaylorCoefficientMatrixComplex
    {κ : Type u} (A B : ℕ)
    (α β : generalBidegreeGrid A B → ℂ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix κ (generalBidegreeGrid A B) ℂ :=
  fun q r => generalBidegreeComplexTaylorCoefficient A B α β (s q) r

/-- The square finite complex Taylor evaluation matrix attached to a finite
enumeration of exponent pairs. -/
noncomputable def generalBidegreeFiniteTaylorEvaluationMatrixComplex
    {κ : Type u} [Fintype κ] (A B : ℕ)
    (α β : generalBidegreeGrid A B → ℂ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℂ :=
  fun r p => ∑ q,
    generalBidegreeComplexTaylorCoefficient A B α β (s q) r *
      generalBidegreeRectangularCoefficientMatrixComplex A B s p q

/-- Exact finite factorization with the same transpose convention as the
real Taylor matrix. -/
theorem generalBidegreeFiniteTaylorEvaluationMatrixComplex_eq_transpose_mul
    {κ : Type u} [Fintype κ] (A B : ℕ)
    (α β : generalBidegreeGrid A B → ℂ)
    (s : κ → generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeFiniteTaylorEvaluationMatrixComplex A B α β s =
      ((generalBidegreeRectangularCoefficientMatrixComplex A B s) *
        (generalBidegreeFiniteTaylorCoefficientMatrixComplex A B α β s)).transpose := by
  ext r p
  simp only [generalBidegreeFiniteTaylorEvaluationMatrixComplex,
    generalBidegreeFiniteTaylorCoefficientMatrixComplex, Matrix.transpose_apply,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- A complex Taylor coefficient has the same inverse-factorial exponential
weight bound as its real counterpart, with absolute values replaced by
complex norms. -/
theorem norm_generalBidegreeComplexTaylorCoefficient_le_invFactorials_mul_exp_neg_realWeight
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (ellM ellX : ℝ)
    (hα : ‖α r‖ ≤ Real.exp (-ellM))
    (hβ : ‖β r‖ ≤ Real.exp (-ellX)) :
    ‖generalBidegreeComplexTaylorCoefficient A B α β m r‖ ≤
      ((Nat.factorial (m 0) : ℝ)⁻¹ *
        (Nat.factorial (m 1) : ℝ)⁻¹) *
          Real.exp (-generalBidegreeRealWeight ellM ellX m) := by
  calc
    ‖generalBidegreeComplexTaylorCoefficient A B α β m r‖ =
        ‖α r‖ ^ (m 0) * ‖β r‖ ^ (m 1) /
          (Nat.factorial (m 0) : ℝ) /
            (Nat.factorial (m 1) : ℝ) := by
      simp [generalBidegreeComplexTaylorCoefficient, norm_pow]
    _ ≤ ((Real.exp (-ellM)) ^ (m 0) *
          (Real.exp (-ellX)) ^ (m 1)) /
            (Nat.factorial (m 0) : ℝ) /
              (Nat.factorial (m 1) : ℝ) := by
      gcongr
    _ = ((Nat.factorial (m 0) : ℝ)⁻¹ *
          (Nat.factorial (m 1) : ℝ)⁻¹) *
            Real.exp (-generalBidegreeRealWeight ellM ellX m) :=
      generalBidegreeTaylor_factorialScale_eq_invFactorials_mul_exp_neg_realWeight
        m ellM ellX

/-- The determinant of a selected complex coefficient minor is literally
the complex cast of the same selected rational coefficient determinant. -/
theorem det_generalBidegreeRectangularCoefficientMatrixComplex_submatrix_eq_ratCast
    {κ : Type u} (A B : ℕ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (p : generalBidegreeGrid A B → κ) :
    ((generalBidegreeRectangularCoefficientMatrixComplex A B s).submatrix
        id p).det =
      algebraMap ℚ ℂ
        ((generalBidegreeSelectedCoefficientEvaluationMatrix A B
          (s ∘ p)).det) := by
  have hmatrix :
      (generalBidegreeRectangularCoefficientMatrix A B s).submatrix id p =
        generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p) := by
    rfl
  change (((algebraMap ℚ ℂ).mapMatrix
    ((generalBidegreeRectangularCoefficientMatrix A B s).submatrix id p)).det) = _
  rw [← (algebraMap ℚ ℂ).map_det, hmatrix]

/-- Nonvanishing of the complex selected minor implies nonvanishing of the
underlying rational minor used by the weighted rank filtration. -/
theorem generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_complex
    {κ : Type u} (A B : ℕ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (p : generalBidegreeGrid A B → κ)
    (hminor :
      ((generalBidegreeRectangularCoefficientMatrixComplex A B s).submatrix
        id p).det ≠ 0) :
    (generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p)).det ≠ 0 := by
  intro hzero
  apply hminor
  rw [det_generalBidegreeRectangularCoefficientMatrixComplex_submatrix_eq_ratCast,
    hzero, map_zero]

/-- Finite complex sheared Taylor determinant decay under an explicit lower
bound for the total weight of every nonzero complex coefficient minor. -/
theorem norm_det_generalBidegreeFiniteTaylorEvaluationMatrixComplex_le_factorial_mul_exp_neg_minWeight_mul_sum_invFactorials_pow
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (C : κ → ℝ) (ellM ellX W : ℝ)
    (hC_nonneg : ∀ q, 0 ≤ C q)
    (hU : ∀ r q,
      ‖generalBidegreeRectangularCoefficientMatrixComplex A B s r q‖ ≤ C q)
    (hweight :
      ∀ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
        ((generalBidegreeRectangularCoefficientMatrixComplex A B s).submatrix
          id p.1).det ≠ 0 →
          W ≤ ∑ i, generalBidegreeRealWeight ellM ellX (s (p.1 i)))
    (hα : ∀ r, ‖α r‖ ≤ Real.exp (-ellM))
    (hβ : ∀ r, ‖β r‖ ≤ Real.exp (-ellX)) :
    ‖(generalBidegreeFiniteTaylorEvaluationMatrixComplex A B α β s).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-W) *
          (∑ q, C q *
            ((Nat.factorial (s q 0) : ℝ)⁻¹ *
              (Nat.factorial (s q 1) : ℝ)⁻¹)) ^
            Fintype.card (generalBidegreeGrid A B) := by
  rw [generalBidegreeFiniteTaylorEvaluationMatrixComplex_eq_transpose_mul,
    Matrix.det_transpose]
  apply norm_det_complex_mul_le_factorial_mul_exp_neg_minWeight_mul_sum_pow
    (generalBidegreeRectangularCoefficientMatrixComplex A B s)
    (generalBidegreeFiniteTaylorCoefficientMatrixComplex A B α β s)
    C
    (fun q => (Nat.factorial (s q 0) : ℝ)⁻¹ *
      (Nat.factorial (s q 1) : ℝ)⁻¹)
    (fun q => generalBidegreeRealWeight ellM ellX (s q)) W
  · exact hC_nonneg
  · intro q
    exact mul_nonneg (by positivity) (by positivity)
  · exact hU
  · intro q r
    exact
      norm_generalBidegreeComplexTaylorCoefficient_le_invFactorials_mul_exp_neg_realWeight
        A B α β (s q) r ellM ellX (hα r) (hβ r)
  · exact hweight

/-- The same determinant estimate with both coefficient hypotheses stated
over the existing real/rational coefficient APIs.  The complex norm bound is
transported from the real absolute-value bound, and complex-minor
nonvanishing is transported to the rational selected minor before the
weight hypothesis is applied. -/
theorem norm_det_generalBidegreeFiniteTaylorEvaluationMatrixComplex_le_of_rationalMinorWeight
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (C : κ → ℝ) (ellM ellX W : ℝ)
    (hC_nonneg : ∀ q, 0 ≤ C q)
    (hU : ∀ r q,
      |generalBidegreeRectangularCoefficientMatrixReal A B s r q| ≤ C q)
    (hweight :
      ∀ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
        (generalBidegreeSelectedCoefficientEvaluationMatrix A B
          (s ∘ p.1)).det ≠ 0 →
          W ≤ ∑ i, generalBidegreeRealWeight ellM ellX (s (p.1 i)))
    (hα : ∀ r, ‖α r‖ ≤ Real.exp (-ellM))
    (hβ : ∀ r, ‖β r‖ ≤ Real.exp (-ellX)) :
    ‖(generalBidegreeFiniteTaylorEvaluationMatrixComplex A B α β s).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-W) *
          (∑ q, C q *
            ((Nat.factorial (s q 0) : ℝ)⁻¹ *
              (Nat.factorial (s q 1) : ℝ)⁻¹)) ^
            Fintype.card (generalBidegreeGrid A B) := by
  apply
    norm_det_generalBidegreeFiniteTaylorEvaluationMatrixComplex_le_factorial_mul_exp_neg_minWeight_mul_sum_invFactorials_pow
      A B α β s C ellM ellX W hC_nonneg
  · intro r q
    rw [norm_generalBidegreeRectangularCoefficientMatrixComplex_eq_abs_real]
    exact hU r q
  · intro p hp
    apply hweight p
    exact
      generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_complex
        A B s p.1 hp
  · exact hα
  · exact hβ

/-- The rational-minor bridge composed with the existing discrete weighted
rank filtration.  This removes the selected-minor weight premise in favor of
the literal mesh-scaled parallel-line rank-deficit sum, while retaining the
finite coefficient/Taylor mass unchanged. -/
theorem norm_det_generalBidegreeFiniteTaylorEvaluationMatrixComplex_le_scaledParallelLineDeficits
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℂ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (C : κ → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hC_nonneg : ∀ q, 0 ≤ C q)
    (hU : ∀ r q,
      |generalBidegreeRectangularCoefficientMatrixReal A B s r q| ≤ C q)
    (hα : ∀ r, ‖α r‖ ≤ Real.exp (-ellM))
    (hβ : ∀ r, ‖β r‖ ≤ Real.exp (-ellX))
    (hmesh : 0 < mesh) (Q : ℕ) :
    ‖(generalBidegreeFiniteTaylorEvaluationMatrixComplex A B α β s).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp
          (-((∑ j ∈ Finset.range Q,
            ((Fintype.card (generalBidegreeGrid A B) -
              generalBidegreePositiveRealWeightedParallelLineRankCap
                A ellM ellX (((j + 1 : ℕ) : ℝ) * mesh)
                  hellM_pos hell : ℕ) : ℝ)) * mesh)) *
          (∑ q, C q *
            ((Nat.factorial (s q 0) : ℝ)⁻¹ *
              (Nat.factorial (s q 1) : ℝ)⁻¹)) ^
            Fintype.card (generalBidegreeGrid A B) := by
  apply
    norm_det_generalBidegreeFiniteTaylorEvaluationMatrixComplex_le_of_rationalMinorWeight
      A B α β s C ellM ellX
        ((∑ j ∈ Finset.range Q,
          ((Fintype.card (generalBidegreeGrid A B) -
            generalBidegreePositiveRealWeightedParallelLineRankCap
              A ellM ellX (((j + 1 : ℕ) : ℝ) * mesh)
                hellM_pos hell : ℕ) : ℝ)) * mesh)
        hC_nonneg hU
  · intro p hp
    simpa only [Function.comp_apply] using
      totalWeight_selectedCoefficientEvaluation_ge_scaledParallelLineDeficits_of_det_ne_zero
        A B (s ∘ p.1)
          (fun i => generalBidegreeRealWeight ellM ellX (s (p.1 i)))
          ellM ellX mesh hellM_pos hell (fun _ => rfl) hp hmesh Q
  · exact hα
  · exact hβ

end PellPaper
