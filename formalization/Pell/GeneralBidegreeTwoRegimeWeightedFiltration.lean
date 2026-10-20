import Pell.GeneralBidegreePositiveRealWeightedShellUpper
import Pell.GeneralBidegreeFiniteTaylorSelection

/-!
# A two-regime greedy filtration on the sheared grid

The finite shell analysis supplies two complementary caps for the rank of a
positive real weighted coefficient ball: the exact triangular floor-sum cap
and the outer-boundary linear shell cap.  This module feeds their pointwise
minimum into the existing mesh-based greedy filtration.  It is a fully finite
counterpart to the two-regime integral in `L:sheared` of `main.tex`.

It does not evaluate the resulting sum asymptotically, nor supply the
analytic determinant decay.
-/

namespace PellPaper

open scoped BigOperators

/-- The pointwise minimum of the triangular and outer-shell rank caps. -/
noncomputable def generalBidegreePositiveRealWeightedTwoRegimeRankCap
    (A : ℕ) (ellM ellX R : ℝ) : ℕ :=
  min (generalBidegreePositiveRealWeightedFloorSum ellM ellX R)
    ((⌊R / ellX⌋₊ + 1) *
      ⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊)

/-- The selected coefficient family inherits the two-regime rank cap from
the ambient sheared-grid coefficient evaluation space. -/
theorem finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_twoRegimeRankCap
    {ι : Type*} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hR : 0 ≤ R) :
    Module.finrank ℚ
      (finiteRealWeightFilteredSpan (K := ℚ)
        (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) ≤
      generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX R := by
  unfold generalBidegreePositiveRealWeightedTwoRegimeRankCap
  exact (finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_positiveBall
    A B s weight ellM ellX R hellM_pos hell hweight).trans
    (generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_twoRegimeEnvelope
      A B ellM ellX R hellM_pos hell hR)

/-- **Finite two-regime greedy lower bound.**  A linearly independent family
of selected coefficient vectors has total logarithmic weight at least the
mesh-scaled sum of deficits from the minimum of the two finite rank caps. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledTwoRegimeDeficits
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hlin : LinearIndependent ℚ
      (generalBidegreeSelectedCoefficientEvaluation A B s))
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card ι -
        generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh ≤
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
      (fun n => generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh)) hlin hmesh hweight_nonneg Q
  intro n _
  apply finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_twoRegimeRankCap
    A B s weight ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell hweight
  exact mul_nonneg (by positivity) hmesh.le

/-- The preceding lower bound with linear independence discharged by a
nonzero selected coefficient determinant. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledTwoRegimeDeficits_of_det_ne_zero
    (A B : ℕ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (weight : generalBidegreeGrid A B → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hdet : (generalBidegreeSelectedCoefficientEvaluationMatrix A B s).det ≠ 0)
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card (generalBidegreeGrid A B) -
        generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh ≤
      ∑ i, weight i := by
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledTwoRegimeDeficits
    A B s weight ellM ellX mesh hellM_pos hell hweight
    (linearIndependent_generalBidegreeSelectedCoefficientEvaluation_of_det_ne_zero
      A B s hdet) hmesh Q

/-- The literal finite Taylor determinant version of the two-regime greedy
bound.  It combines finite Taylor minor selection with the sharper pointwise
minimum of the triangular and linear shell rank caps. -/
theorem exists_injective_selectedTwoRegimeWeightBound_of_det_finiteTaylor_ne_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
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
          generalBidegreePositiveRealWeightedTwoRegimeRankCap
            A ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh ≤
        ∑ i, weight (p.1 i) := by
  rcases exists_injective_selectedCoefficientMinor_of_det_finiteTaylor_ne_zero
    A B α β s hdet with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledTwoRegimeDeficits_of_det_ne_zero
    A B (s ∘ p.1) (weight ∘ p.1) ellM ellX mesh hellM_pos hell ?_ hp hmesh Q
  intro i
  exact hweight (p.1 i)

end PellPaper
