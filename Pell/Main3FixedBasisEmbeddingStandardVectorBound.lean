import Pell.Main3LargeAnalyticFixedKeyCellTargetLatticeGeometry
import Mathlib.Tactic

/-!
# Fixed-basis generator and standard-vector embedding bounds

The displayed integral-basis generator has trace parameter `t = 0` or `1`,
while its difference from its quadratic conjugate has norm equal to the square
root of the field discriminant.  Combining these identities with the proved
quadratic discriminant upper bound controls both embedded generators by
`2 * sqrt |a|` at every complex embedding.  In particular, the estimate applies
uniformly to the explicit real and imaginary places used by the two main3
branches.

The final theorem records the form needed by the bounded-completion argument:
the target linear form on either standard integral vector has the same bound.
No cell geometry or analytic estimate is used.
-/

namespace PellPaper

noncomputable section

local instance main3FixedBasisEmbeddingStandardVectorBound_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

private theorem shiftedSquareFixedBasis_embeddingGenerator_norm_pair_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha0 : a ≠ 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma (F.omega : rationalQuadraticAlgebra (-a))‖ ≤
        2 * Real.sqrt |(a : ℝ)| ∧
      ‖sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ ≤
        2 * Real.sqrt |(a : ℝ)| := by
  have hsqrtOne : 1 ≤ Real.sqrt |(a : ℝ)| := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Int.one_le_abs ha0)
  have hdiffSq := shiftedSquareFixedBasis_embeddingDifference_norm_sq F sigma
  have hdiff :
      ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
          sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ =
        Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
    calc
      ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
          sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ =
          Real.sqrt
            (‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
                sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
        congr 1
        rw [← map_sub]
        exact hdiffSq
  have hdiffBound :
      ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
          sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ ≤
        2 * Real.sqrt |(a : ℝ)| := by
    rw [hdiff]
    exact sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a
  have hadd := shiftedSquare_displayedOmega_add_star_eq
    F.basis F.omega F.t F.c F.basis_zero F.basis_one F.omega_sq
  have haddSigma :
      sigma (F.omega : rationalQuadraticAlgebra (-a)) +
          sigma (star (F.omega : rationalQuadraticAlgebra (-a))) =
        (F.t : ℂ) := by
    simpa only [map_add, map_intCast] using congrArg sigma hadd
  have htNorm : ‖(F.t : ℂ)‖ ≤ 1 := by
    rcases F.t_zero_or_one with ht | ht <;> simp [ht]
  constructor
  · have htwice :
        2 * ‖sigma (F.omega : rationalQuadraticAlgebra (-a))‖ ≤
          1 + 2 * Real.sqrt |(a : ℝ)| := by
      calc
        2 * ‖sigma (F.omega : rationalQuadraticAlgebra (-a))‖ =
            ‖(2 : ℂ) * sigma (F.omega : rationalQuadraticAlgebra (-a))‖ := by
          rw [norm_mul]
          norm_num
        _ = ‖(F.t : ℂ) +
            (sigma (F.omega : rationalQuadraticAlgebra (-a)) -
              sigma (star (F.omega : rationalQuadraticAlgebra (-a))))‖ := by
          congr 1
          linear_combination haddSigma
        _ ≤ ‖(F.t : ℂ)‖ +
            ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
              sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ :=
          norm_add_le _ _
        _ ≤ 1 + 2 * Real.sqrt |(a : ℝ)| :=
          add_le_add htNorm hdiffBound
    nlinarith
  · have htwice :
        2 * ‖sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ ≤
          1 + 2 * Real.sqrt |(a : ℝ)| := by
      calc
        2 * ‖sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ =
            ‖(2 : ℂ) *
              sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ := by
          rw [norm_mul]
          norm_num
        _ = ‖(F.t : ℂ) -
            (sigma (F.omega : rationalQuadraticAlgebra (-a)) -
              sigma (star (F.omega : rationalQuadraticAlgebra (-a))))‖ := by
          congr 1
          linear_combination haddSigma
        _ ≤ ‖(F.t : ℂ)‖ +
            ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
              sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ := by
          exact norm_sub_le _ _
        _ ≤ 1 + 2 * Real.sqrt |(a : ℝ)| :=
          add_le_add htNorm hdiffBound
    nlinarith

/-- Every complex embedding of the fixed displayed generator has norm at
most `2 * sqrt |a|`.  This applies in particular at the explicit positive
real and imaginary places. -/
theorem shiftedSquareFixedBasis_embeddingGenerator_norm_le_two_mul_sqrt_abs
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha0 : a ≠ 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma (F.omega : rationalQuadraticAlgebra (-a))‖ ≤
      2 * Real.sqrt |(a : ℝ)| :=
  (shiftedSquareFixedBasis_embeddingGenerator_norm_pair_le ha0 F sigma).1

/-- The same bound holds after applying quadratic conjugation to the fixed
displayed generator. -/
theorem shiftedSquareFixedBasis_embeddingStarGenerator_norm_le_two_mul_sqrt_abs
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha0 : a ≠ 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ ≤
      2 * Real.sqrt |(a : ℝ)| :=
  (shiftedSquareFixedBasis_embeddingGenerator_norm_pair_le ha0 F sigma).2

/-- Evaluating the fixed-basis target linear form on either standard integral
vector costs at most `2 * sqrt |a|`. -/
theorem norm_main3IntegralTargetLinearForm_standardVector_le_two_mul_sqrt_abs
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha0 : a ≠ 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) (i : Fin 2) :
    ‖main3IntegralTargetLinearForm
        (sigma (F.omega : rationalQuadraticAlgebra (-a)))
        (Pi.single i (1 : ℤ))‖ ≤
      2 * Real.sqrt |(a : ℝ)| := by
  have hsqrtOne : 1 ≤ Real.sqrt |(a : ℝ)| := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Int.one_le_abs ha0)
  fin_cases i
  · norm_num [main3IntegralTargetLinearForm, Pi.single_apply]
    nlinarith
  · simpa [main3IntegralTargetLinearForm, Pi.single_apply] using
      shiftedSquareFixedBasis_embeddingGenerator_norm_le_two_mul_sqrt_abs
        ha0 F sigma

end

end PellPaper
