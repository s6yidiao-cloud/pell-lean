import Pell.FiniteRealWeightedRankFiltration
import Pell.GeneralBidegreePositiveRealWeightedRank

/-!
# Selected real-weight coefficient filtrations on the sheared grid

This module connects the generic finite real-weight rank-filtration machinery
to the literal coefficient vectors `(a + 2b)^i b^j` occurring in the
sheared Taylor expansion.  A selected finite family of exponent pairs maps to
grid-evaluation vectors; its real low-weight span is bounded by the ambient
positive real weighted-ball evaluation rank.

The selection still has to be supplied with a linear-independence certificate
(for example from a nonzero coefficient minor).  The analytic Taylor limit is
not addressed here.
-/

namespace PellPaper

open scoped BigOperators

universe u

/-- Evaluate the ordinary coefficient monomial indexed by a selected Taylor
exponent on the sheared grid. -/
noncomputable def generalBidegreeSelectedCoefficientEvaluation
    {ι : Type u} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex) :
    ι → (generalBidegreeGrid A B → ℚ) :=
  fun i => generalBidegreeGridPolynomialEvaluationLinearMap A B
    (MvPolynomial.monomial (s i) (1 : ℚ))

/-- The square coefficient-minor matrix for a selected enumeration indexed by
the full sheared grid.  Its columns are the selected coefficient vectors. -/
noncomputable def generalBidegreeSelectedCoefficientEvaluationMatrix
    (A B : ℕ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℚ :=
  fun p q => generalBidegreeSelectedCoefficientEvaluation A B s q p

/-- A nonzero selected coefficient minor gives the linear independence needed
by the real weighted greedy filtration. -/
theorem linearIndependent_generalBidegreeSelectedCoefficientEvaluation_of_det_ne_zero
    (A B : ℕ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (hdet : (generalBidegreeSelectedCoefficientEvaluationMatrix A B s).det ≠ 0) :
    LinearIndependent ℚ (generalBidegreeSelectedCoefficientEvaluation A B s) := by
  have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  change LinearIndependent ℚ
    (fun q p => generalBidegreeSelectedCoefficientEvaluation A B s q p) at hcols
  exact hcols

/-- If every selected low-weight exponent belongs to an ambient finite
support, its grid-evaluation span is contained in the ambient evaluation
range. -/
theorem finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_range
    {ι : Type u} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (R : ℝ)
    (U : Finset generalBidegreeCoefficientMonomialIndex)
    (hsupport : ∀ i, weight i ≤ R → s i ∈ U) :
    finiteRealWeightFilteredSpan (K := ℚ)
      (generalBidegreeSelectedCoefficientEvaluation A B s) weight R ≤
      LinearMap.range
        ((generalBidegreeGridPolynomialEvaluationLinearMap A B).domRestrict
          (generalBidegreeCoefficientMonomialSpan U)) := by
  classical
  unfold finiteRealWeightFilteredSpan
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  refine ⟨⟨MvPolynomial.monomial (s i.1) (1 : ℚ), ?_⟩, ?_⟩
  · unfold generalBidegreeCoefficientMonomialSpan
    apply Submodule.subset_span
    change MvPolynomial.monomial (s i.1) (1 : ℚ) ∈
      generalBidegreeCoefficientMonomialFinset U
    unfold generalBidegreeCoefficientMonomialFinset
    exact Finset.mem_image.mpr ⟨s i.1, hsupport i.1 i.2, rfl⟩
  · rfl

/-- The preceding containment as a finite-rank inequality. -/
theorem finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le
    {ι : Type u} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (R : ℝ)
    (U : Finset generalBidegreeCoefficientMonomialIndex)
    (hsupport : ∀ i, weight i ≤ R → s i ∈ U) :
    Module.finrank ℚ
      (finiteRealWeightFilteredSpan (K := ℚ)
        (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) ≤
      generalBidegreeCoefficientEvaluationRank A B U := by
  unfold generalBidegreeCoefficientEvaluationRank
  exact Submodule.finrank_mono
    (finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_range
      A B s weight R U hsupport)

/-- The selected real-weight coefficient span is controlled by the literal
untruncated positive real weighted ball whenever the declared selection
weight is the monomial's logarithmic weight. -/
theorem finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_positiveBall
    {ι : Type u} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i)) :
    Module.finrank ℚ
      (finiteRealWeightFilteredSpan (K := ℚ)
        (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) ≤
      generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) := by
  apply finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le
    A B s weight R
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell)
  intro i hi
  rw [mem_generalBidegreePositiveRealWeightedBall_iff, ← hweight i]
  exact hi

/-- The exact natural-valued upper cap furnished by the parallel-line
kernel at one real radius. -/
noncomputable def generalBidegreePositiveRealWeightedParallelLineRankCap
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) : ℕ :=
  (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
    (generalBidegreePositiveRealWeightedBall ellM ellX
      (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card

/-- The exact selected-family version of the parallel-line rank cap in
`L:sheared`.  It is ready to feed the real greedy filtration once a selected
coefficient minor supplies linear independence. -/
theorem finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_parallelLineDefect
    {ι : Type u} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i)) :
    Module.finrank ℚ
      (finiteRealWeightFilteredSpan (K := ℚ)
        (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) ≤
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card := by
  exact (finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_positiveBall
    A B s weight ellM ellX R hellM_pos hell hweight).trans
    (generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
      A B ellM ellX R hellM_pos hell)

/-- Named-cap form of the exact selected-family parallel-line rank bound. -/
theorem finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_parallelLineRankCap
    {ι : Type u} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i)) :
    Module.finrank ℚ
      (finiteRealWeightFilteredSpan (K := ℚ)
        (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) ≤
      generalBidegreePositiveRealWeightedParallelLineRankCap
        A ellM ellX R hellM_pos hell := by
  simpa [generalBidegreePositiveRealWeightedParallelLineRankCap] using
    finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_parallelLineDefect
      A B s weight ellM ellX R hellM_pos hell hweight

/-- **Discrete sheared greedy bound for a selected Taylor family.**  Once a
selected coefficient minor gives linear independence, the exact real
parallel-line rank cap supplies a mesh-scaled lower bound for its total
logarithmic weight.  This is the finite, discretized counterpart of the
rank-filtration step in `L:sheared`. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledParallelLineDeficits
    {ι : Type u} [Fintype ι] (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hlin : LinearIndependent ℚ
      (generalBidegreeSelectedCoefficientEvaluation A B s))
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card ι -
        generalBidegreePositiveRealWeightedParallelLineRankCap
          A ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℕ) : ℝ)) * mesh ≤
      ∑ i, weight i := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    rw [hweight i, generalBidegreeRealWeight]
    exact add_nonneg
      (mul_nonneg (by positivity) hellM_pos.le)
      (mul_nonneg (by positivity) hellX_pos.le)
  apply totalRealWeight_ge_scaledRealRankCapDeficit
    (K := ℚ) (generalBidegreeSelectedCoefficientEvaluation A B s) weight mesh
      (fun n => generalBidegreePositiveRealWeightedParallelLineRankCap
        A ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell)
      hlin hmesh hweight_nonneg Q
  intro n _
  exact finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_parallelLineRankCap
    A B s weight ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell hweight

/-- The preceding discrete greedy bound with the linear-independence premise
discharged by a nonzero selected coefficient minor. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledParallelLineDeficits_of_det_ne_zero
    (A B : ℕ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (weight : generalBidegreeGrid A B → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hdet : (generalBidegreeSelectedCoefficientEvaluationMatrix A B s).det ≠ 0)
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card (generalBidegreeGrid A B) -
        generalBidegreePositiveRealWeightedParallelLineRankCap
          A ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℕ) : ℝ)) * mesh ≤
      ∑ i, weight i := by
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledParallelLineDeficits
    A B s weight ellM ellX mesh hellM_pos hell hweight
      (linearIndependent_generalBidegreeSelectedCoefficientEvaluation_of_det_ne_zero
        A B s hdet) hmesh Q

end PellPaper
