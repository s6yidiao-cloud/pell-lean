import Pell.GeneralBidegreeSelectedRealWeightedFiltration

/-!
# Greedy filtration by literal positive-ball ranks

The sharp shifted high branch is most naturally compared with the *actual*
coefficient-evaluation rank of each weighted ball.  This module supplies the
minimal filtration bridge: every independent selected coefficient family has
total weight at least the mesh sum of those literal rank deficits.  It makes
no choice of a continuous envelope, so a source-specific low/high cap can be
inserted afterwards without changing the Taylor-decay core.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The literal rank deficit of one positive real weighted coefficient ball
inside an ambient family of size `H`. -/
def generalBidegreePositiveRealWeightedRankDeficit
    (A B H : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) : ℕ :=
  H - generalBidegreeCoefficientEvaluationRank A B
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell)

/-- The selected real-weight filtration is bounded below by the mesh sum of
literal positive-ball rank deficits. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledActualPositiveBallRankDeficits
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (weight : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hlin : LinearIndependent ℚ
      (generalBidegreeSelectedCoefficientEvaluation A B s))
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      (generalBidegreePositiveRealWeightedRankDeficit A B (Fintype.card ι)
        ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh ≤
      ∑ i, weight i := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    rw [hweight i, generalBidegreeRealWeight]
    exact add_nonneg
      (mul_nonneg (by positivity) hellM_pos.le)
      (mul_nonneg (by positivity) hellX_pos.le)
  change (∑ n ∈ Finset.range Q,
    ((Fintype.card ι - generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell) : ℕ) : ℝ)) * mesh ≤
      ∑ i, weight i
  apply totalRealWeight_ge_scaledRealRankCapDeficit
    (K := ℚ) (generalBidegreeSelectedCoefficientEvaluation A B s) weight mesh
      (fun n => generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell))
      hlin hmesh hweight_nonneg Q
  intro n _
  exact finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_positiveBall
    A B s weight ellM ellX (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell hweight

/-- The literal-rank filtration bound with linear independence discharged by
a nonzero selected coefficient determinant. -/
theorem totalWeight_selectedCoefficientEvaluation_ge_scaledActualPositiveBallRankDeficits_of_det_ne_zero
    (A B : ℕ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (weight : generalBidegreeGrid A B → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hweight : ∀ i, weight i = generalBidegreeRealWeight ellM ellX (s i))
    (hdet : (generalBidegreeSelectedCoefficientEvaluationMatrix A B s).det ≠ 0)
    (hmesh : 0 < mesh) (Q : ℕ) :
    (∑ n ∈ Finset.range Q,
      (generalBidegreePositiveRealWeightedRankDeficit A B
        (Fintype.card (generalBidegreeGrid A B)) ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh ≤
      ∑ i, weight i := by
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledActualPositiveBallRankDeficits
    A B s weight ellM ellX mesh hellM_pos hell hweight
      (linearIndependent_generalBidegreeSelectedCoefficientEvaluation_of_det_ne_zero
        A B s hdet) hmesh Q

/-- Under exact low-endpoint alignment, the contiguous mesh deficit sum
splits into the low mesh and the translated high mesh used by the two-regime
sheared cubic calculation.  The rank deficit is left literal, so this lemma
applies to any later shifted-cap comparison. -/
theorem sum_actualPositiveBallRankDeficits_low_high_eq_contiguous
    (A B H : ℕ) (ellM ellX mesh x rho : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (Nlow Nhigh : ℕ)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho) :
    (∑ n ∈ Finset.range Nlow,
      (generalBidegreePositiveRealWeightedRankDeficit A B H ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) +
      ∑ n ∈ Finset.range Nhigh,
        (generalBidegreePositiveRealWeightedRankDeficit A B H ellM ellX
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ) =
      ∑ n ∈ Finset.range (Nlow + Nhigh),
        (generalBidegreePositiveRealWeightedRankDeficit A B H ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    (generalBidegreePositiveRealWeightedRankDeficit A B H ellM ellX
      (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)
  have hhigh :
      (∑ n ∈ Finset.range Nhigh,
        (generalBidegreePositiveRealWeightedRankDeficit A B H ellM ellX
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) =
        ∑ n ∈ Finset.range Nhigh, f (Nlow + n) := by
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f]
    rw [← hlow_align]
    push_cast
    ring_nf
  change (∑ n ∈ Finset.range Nlow, f n) +
      ∑ n ∈ Finset.range Nhigh,
        (generalBidegreePositiveRealWeightedRankDeficit A B H ellM ellX
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ) =
      ∑ n ∈ Finset.range (Nlow + Nhigh), f n
  rw [hhigh]
  have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_add_right Nlow Nhigh)
  rw [Finset.sum_Ico_eq_sum_range] at hsplit
  simpa [Nat.add_sub_cancel_left] using hsplit

end

end PellPaper
