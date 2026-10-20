import Pell.SourceTargetSlopeWindowTransfer
import Pell.DyadicSourceRatioNormalizedCenters

/-!
# Actual source-cell multiplicity over a target ceiling index

This is a literal relation between the project's geometric source cells and
the integer target ceiling index of their actual factor tuples.  The factor
equation, dyadic lower endpoints, scale comparison, center range and source
separation are derived from those cells.  Under `M≤E²V`, any fixed target
index is supported by at most 337 active source indices.
No curve-point count or weighted/minimum-sum transfer is asserted.
-/

namespace PellPaper

noncomputable section

/-- The actual dyadic endpoint scale ratio `D²U/(E²V)`. -/
def dyadicSourceTargetScaleRatio (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  sourceTargetScaleRatio ((2 ^ i.1 : ℕ) : ℝ) ((2 ^ i.2.1 : ℕ) : ℝ)
    ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ)

/-- The right-ceiling target index of an actual natural factor tuple. -/
def dyadicFactorBoxTargetRightIndex (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (q : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  targetSlopeRightIndex ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ)
    (M : ℝ) (q.2.2.1 : ℤ) (q.2.2.2 : ℤ)

/-- Every actual point of a geometric source cell satisfies the proved
quadratic target-index window, with no supplied error/range hypothesis. -/
theorem dyadicFactorBoxLocalRatioCell_targetRightIndex_window
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {M j : ℕ}
    (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ dyadicFactorBoxLocalRatioCell theta Y i M j) :
    |(dyadicFactorBoxTargetRightIndex i M q : ℝ) -
      quadraticTargetCenter (M : ℝ) (dyadicSourceTargetScaleRatio i)
        (dyadicFactorBoxLocalRatioNormalizedCenter i M j)| ≤ 12 * dyadicSourceTargetScaleRatio i + 3 := by
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let E : ℝ := ((2 ^ i.2.1 : ℕ) : ℝ)
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM.ne'
  have hqambient := (mem_dyadicFactorBoxLocalRatioCell hq).1
  have hqbox : (q.1, q.2.1, q.2.2.1, q.2.2.2) ∈ dyadicBox i := (Finset.mem_inter.mp hqambient).2
  have hcond : DyadicFactorCondition theta Y q.1 q.2.1 q.2.2.1 q.2.2.2 :=
    mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hqambient).1
  have hlower := dyadicBox_coordinate_lower_bounds hqbox
  have hcell := dyadicFactorBoxLocalRatioCell_commonWindow hq
  have hs₀ : 0 ≤ dyadicFactorBoxLocalRatioCenter i M j := by
    unfold dyadicFactorBoxLocalRatioCenter dyadicFactorBoxLocalRatioStart localRatioMeshStep
    positivity
  have hzupper := dyadicFactorBoxLocalRatioNormalizedCenter_upper_of_nonempty theta Y i M j ⟨q, hq⟩
  obtain ⟨h, hh, hdiff⟩ := dyadicFactorCondition_exists_difference hcond
  have hdiffR : |(q.2.1 : ℝ) ^ 2 * (q.2.2.2 : ℝ) - (q.1 : ℝ) ^ 2 * (q.2.2.1 : ℝ)| ≤ 2 := by
    have heq : (q.2.1 : ℝ) ^ 2 * (q.2.2.2 : ℝ) - (q.1 : ℝ) ^ 2 * (q.2.2.1 : ℝ) = (h : ℝ) := by
      exact_mod_cast hdiff
    rw [heq]
    rcases hh with rfl | rfl | rfl | rfl <;> norm_num
  have hwindow := targetSlopeRightIndex_within_source_window D E U V (M : ℝ)
    (dyadicFactorBoxLocalRatioCenter i M j) hD hE hU hV hMone hs₀
    hzupper (q.1 : ℤ) (q.2.1 : ℤ) (q.2.2.1 : ℤ) (q.2.2.2 : ℤ)
    (by dsimp [E]; exact_mod_cast hlower.2.1) (by dsimp [U]; exact_mod_cast hlower.2.2.1)
    (by simpa only [Int.cast_natCast] using hcell) hscale
    (by simpa only [Int.cast_natCast] using hdiffR)
  exact hwindow

/-- The active geometric source indices containing an actual tuple with
the specified target ceiling index. -/
def dyadicSourceIndicesForTargetIndex
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (k : ℤ) : Finset ℕ := by
  classical
  exact (activeDyadicSourceRatioIndices theta Y i M).filter fun j =>
    ∃ q ∈ dyadicFactorBoxLocalRatioCell theta Y i M j, dyadicFactorBoxTargetRightIndex i M q = k

/-- The actual source/target incidence relation is contained in the genuine
quadratic-center window, not a presumed bounded-multiplicity relation. -/
theorem dyadicSourceIndicesForTargetIndex_subset_window
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) (k : ℤ) :
    dyadicSourceIndicesForTargetIndex theta Y i M k ⊆
      quadraticTargetWindowIndices (activeDyadicSourceRatioIndices theta Y i M)
        (dyadicFactorBoxLocalRatioNormalizedCenter i M) (M : ℝ) (dyadicSourceTargetScaleRatio i)
        (k : ℝ) (12 * dyadicSourceTargetScaleRatio i + 3) := by
  intro j hj
  have hmem := Finset.mem_filter.mp hj
  obtain ⟨q, hq, hindex⟩ := hmem.2
  refine Finset.mem_filter.mpr ⟨hmem.1, ?_⟩
  have hwindow := dyadicFactorBoxLocalRatioCell_targetRightIndex_window hM hscale hq
  rw [hindex] at hwindow
  simpa only [abs_sub_comm] using hwindow

/-- At most 337 actual geometric source cells support any one integer target
index.  Scale comparability and source-center separation are derived internally. -/
theorem card_dyadicSourceIndicesForTargetIndex_le_337
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) (k : ℤ) :
    (dyadicSourceIndicesForTargetIndex theta Y i M k).card ≤ 337 := by
  classical
  by_cases hne : (dyadicSourceIndicesForTargetIndex theta Y i M k).Nonempty
  · obtain ⟨j, hj⟩ := hne
    obtain ⟨q, hq, _⟩ := (Finset.mem_filter.mp hj).2
    have hqambient := (mem_dyadicFactorBoxLocalRatioCell hq).1
    have hqbox : (q.1, q.2.1, q.2.2.1, q.2.2.2) ∈ dyadicBox i := (Finset.mem_inter.mp hqambient).2
    have hcond : DyadicFactorCondition theta Y q.1 q.2.1 q.2.2.1 q.2.2.2 :=
      mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hqambient).1
    have hcompare := (dyadicFactorCondition_dyadicBox_endpoint_scales_comparable hcond hqbox).1
    have hR : 1 / 24 ≤ dyadicSourceTargetScaleRatio i := by
      unfold dyadicSourceTargetScaleRatio sourceTargetScaleRatio
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hbound := card_quadraticTargetWindowIndices_le_337
      (activeDyadicSourceRatioIndices theta Y i M) (dyadicFactorBoxLocalRatioNormalizedCenter i M)
      (M : ℝ) (dyadicSourceTargetScaleRatio i) (k : ℝ) hMpos hR
      (fun j _ => dyadicFactorBoxLocalRatioNormalizedCenter_lower i M j)
      (fun _ _ _ _ hneq => dyadicFactorBoxLocalRatioNormalizedCenter_separated i hM hneq)
    exact (Finset.card_le_card
      (dyadicSourceIndicesForTargetIndex_subset_window theta Y i hM hscale k)).trans hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end

end PellPaper
