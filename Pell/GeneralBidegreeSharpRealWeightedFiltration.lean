import Pell.GeneralBidegreePositiveRealWeightedSharpTwoRegime
import Pell.GeneralBidegreeSelectedRealWeightedFiltration

/-!
# Sharp real-envelope greedy filtration for the sheared coefficient grid

The sharp two-regime rank cap is naturally real valued: its low branch has a
half-area main term and explicit boundary terms.  This module rounds that
envelope only at the interface to the finite rank-filtration lemma, then
removes the rounding again in the resulting real deficit sum.  It is the
finite bridge needed before comparing the mesh sum to the continuous cubic
integral.
-/

namespace PellPaper

open scoped BigOperators

/-- The sharp continuous rank envelope at one positive weight radius. -/
noncomputable def generalBidegreeSharpTwoRegimeAreaEnvelope
    (A : ℕ) (ellM ellX R : ℝ) : ℝ :=
  min
    (R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1)
    ((R / ellX + 1) * (((((A + 1 : ℕ) : ℝ) * ellX) / ellM) + 1))

/-- The sharp real envelope is nonnegative at every nonnegative radius. -/
theorem generalBidegreeSharpTwoRegimeAreaEnvelope_nonneg
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM)
    (hell : ellM ≤ ellX) (hR : 0 ≤ R) :
    0 ≤ generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX R := by
  unfold generalBidegreeSharpTwoRegimeAreaEnvelope
  apply le_min
  · have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
    positivity
  · have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
    positivity

/-- The selected coefficient span has rank at most the natural floor of the
sharp real two-regime envelope. -/
theorem finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_floor_sharpTwoRegimeAreaEnvelope
    {ι : Type*} (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hR : 0 ≤ R) :
    Module.finrank ℚ
      (finiteRealWeightFilteredSpan (K := ℚ)
        (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) ≤
      ⌊generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX R⌋₊ := by
  apply Nat.le_floor
  have hselected :=
    finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_positiveBall
      A B s weight ellM ellX R hellM_pos hell hweight
  have hselected_cast :
      (Module.finrank ℚ
        (finiteRealWeightFilteredSpan (K := ℚ)
          (generalBidegreeSelectedCoefficientEvaluation A B s) weight R) : ℝ) ≤
        (generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℝ) := by
    exact_mod_cast hselected
  exact hselected_cast.trans (by
    simpa [generalBidegreeSharpTwoRegimeAreaEnvelope] using
      generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_sharpTwoRegimeAreaEnvelope
        A B ellM ellX R hellM_pos hell hR)

/-- **Sharp real-envelope greedy bound.**  Every linearly independent selected
coefficient family has total real weight at least the mesh-scaled sum of the
deficits from the sharp continuous two-regime envelope.  The natural floor
needed by finite-dimensional rank theory is eliminated from the conclusion. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledSharpAreaDeficits
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hlin : LinearIndependent ℚ
      (generalBidegreeSelectedCoefficientEvaluation A B s))
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card ι : ℝ) -
        generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh))) * mesh ≤
      ∑ i, weight i := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    rw [hweight i, generalBidegreeRealWeight]
    exact add_nonneg
      (mul_nonneg (by positivity) hellM_pos.le)
      (mul_nonneg (by positivity) hellX_pos.le)
  let rankCap : ℕ → ℕ := fun n =>
    ⌊generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
      (((n + 1 : ℕ) : ℝ) * mesh)⌋₊
  have hnat := totalRealWeight_ge_scaledRealRankCapDeficit
    (K := ℚ) (generalBidegreeSelectedCoefficientEvaluation A B s) weight mesh
      rankCap hlin hmesh hweight_nonneg Q (by
        intro n hn
        apply
          finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_floor_sharpTwoRegimeAreaEnvelope
            A B s weight ellM ellX _ hellM_pos hell hweight
        exact mul_nonneg (by positivity) hmesh.le)
  have hterm : ∀ n ∈ Finset.range Q,
      (Fintype.card ι : ℝ) -
          generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
            (((n + 1 : ℕ) : ℝ) * mesh) ≤
        ((Fintype.card ι - rankCap n : ℕ) : ℝ) := by
    intro n hn
    let E : ℝ := generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
      (((n + 1 : ℕ) : ℝ) * mesh)
    have hR : 0 ≤ ((n + 1 : ℕ) : ℝ) * mesh :=
      mul_nonneg (by positivity) hmesh.le
    have hE_nonneg : 0 ≤ E :=
      generalBidegreeSharpTwoRegimeAreaEnvelope_nonneg
        A ellM ellX _ hellM_pos hell hR
    have hfloor : ((⌊E⌋₊ : ℕ) : ℝ) ≤ E := Nat.floor_le hE_nonneg
    change (Fintype.card ι : ℝ) - E ≤
      ((Fintype.card ι - ⌊E⌋₊ : ℕ) : ℝ)
    by_cases hfloor_card : ⌊E⌋₊ ≤ Fintype.card ι
    · rw [Nat.cast_sub hfloor_card]
      linarith
    · have hcard_floor : Fintype.card ι ≤ ⌊E⌋₊ :=
        Nat.le_of_not_ge hfloor_card
      rw [Nat.sub_eq_zero_of_le hcard_floor]
      have hcard_cast : (Fintype.card ι : ℝ) ≤ (⌊E⌋₊ : ℝ) := by
        exact_mod_cast hcard_floor
      linarith
  have hsum :
      (∑ n ∈ Finset.range Q,
        ((Fintype.card ι : ℝ) -
          generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
            (((n + 1 : ℕ) : ℝ) * mesh))) ≤
      ∑ n ∈ Finset.range Q, ((Fintype.card ι - rankCap n : ℕ) : ℝ) := by
    let F : ℕ → ℝ := fun n =>
      (Fintype.card ι : ℝ) -
        generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh)
    let G : ℕ → ℝ := fun n => ((Fintype.card ι - rankCap n : ℕ) : ℝ)
    change (∑ n ∈ Finset.range Q, F n) ≤ ∑ n ∈ Finset.range Q, G n
    apply Finset.sum_le_sum
    intro n hn
    exact hterm n hn
  exact (mul_le_mul_of_nonneg_right hsum hmesh.le).trans hnat

/-- The sharp real-envelope greedy bound with linear independence obtained
from a nonzero selected coefficient determinant. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledSharpAreaDeficits_of_det_ne_zero
    (A B : ℕ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (weight : generalBidegreeGrid A B → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hdet : (generalBidegreeSelectedCoefficientEvaluationMatrix A B s).det ≠ 0)
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card (generalBidegreeGrid A B) : ℝ) -
        generalBidegreeSharpTwoRegimeAreaEnvelope A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh))) * mesh ≤
      ∑ i, weight i := by
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledSharpAreaDeficits
    A B s weight ellM ellX mesh hellM_pos hell hweight
    (linearIndependent_generalBidegreeSelectedCoefficientEvaluation_of_det_ne_zero
      A B s hdet) hmesh Q

end PellPaper
