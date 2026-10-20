import Pell.DyadicSourceTargetIndexMultiplicity

/-!
# All actual source-cell / target-center pairs

The pair set is a literal filtered product: a geometric source index and an
integer right-ceiling target center occur precisely when an actual factor
tuple witnesses their incidence.  Every actual tuple is covered, including
the weak lower endpoints of the project's `Ico` dyadic boxes.  No single
representative is chosen for a source cell.

The proved reverse multiplicity transports the sum of actual reciprocal
first minima to this entire pair set, with coefficient `337 * 64 = 21568`.
This establishes finite cover bookkeeping and weighted transport, not a
curve-point count or determinant estimate.
-/

namespace PellPaper

noncomputable section

open scoped Finset

private theorem targetSlopeRightIndex_mem_integerCenters_weak
    (U V M : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M)
    (u v : ℤ) (hu : U ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * U)
    (hv : V ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * V) :
    targetSlopeRightIndex U V M u v ∈ targetSlopeIntegerCenters M := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hupos : 0 < (u : ℝ) := hU.trans_le hu.1
  let r := M * U * (v : ℝ) / (V * (u : ℝ))
  have hrlo : M / 2 ≤ r := by
    apply (le_div_iff₀ (mul_pos hV hupos)).mpr
    calc
      (M / 2) * (V * (u : ℝ)) ≤ (M / 2) * (V * (2 * U)) := by gcongr; exact hu.2
      _ = M * U * V := by ring
      _ ≤ M * U * (v : ℝ) := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  have hrhi : r ≤ 2 * M := by
    apply (div_le_iff₀ (mul_pos hV hupos)).mpr
    calc
      M * U * (v : ℝ) ≤ M * U * (2 * V) := mul_le_mul_of_nonneg_left hv.2 (by positivity)
      _ = (2 * M * V) * U := by ring
      _ ≤ (2 * M * V) * (u : ℝ) := mul_le_mul_of_nonneg_left hu.1 (by positivity)
      _ = (2 * M) * (V * (u : ℝ)) := by ring
  have hklo : M / 2 ≤ (targetSlopeRightIndex U V M u v : ℝ) := hrlo.trans (Int.le_ceil r)
  have hkhi : (targetSlopeRightIndex U V M u v : ℝ) ≤ 3 * M := by
    have hceil : (targetSlopeRightIndex U V M u v : ℝ) < r + 1 := Int.ceil_lt_add_one r
    linarith
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hklo, Int.le_floor.mpr hkhi⟩

/-- The literal `Ico` target coordinates of every actual dyadic-box tuple
have their right-ceiling index in the finite integer-center interval. -/
theorem dyadicFactorBoxTargetRightIndex_mem_integerCenters
    {i : ℕ × ℕ × ℕ × ℕ} {M : ℕ} (hM : 0 < M)
    {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ dyadicBox i) :
    dyadicFactorBoxTargetRightIndex i M q ∈ targetSlopeIntegerCenters (M : ℝ) := by
  have hl := dyadicBox_coordinate_lower_bounds hq
  have hu := dyadicBox_coordinate_upper_bounds hq
  apply targetSlopeRightIndex_mem_integerCenters_weak
    ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ) (M : ℝ)
    (by positivity) (by positivity) (by exact_mod_cast hM)
  · exact ⟨by exact_mod_cast hl.2.2.1, by exact_mod_cast hu.2.2.1⟩
  · exact ⟨by exact_mod_cast hl.2.2.2, by exact_mod_cast hu.2.2.2⟩

private theorem targetSlopeRightIndex_supNorm_le_two_weak
    (U V M : ℝ) (hU : 0 < U) (hV : 0 < V)
    (u v : ℤ) (hu : U ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * U) :
    slopeVectorSupNorm U V M (targetSlopeRightIndex U V M u v : ℝ) (v, u) ≤ 2 := by
  have hupos : 0 < (u : ℝ) := hU.trans_le hu.1
  let r := M * U * (v : ℝ) / (V * (u : ℝ))
  let k := targetSlopeRightIndex U V M u v
  have hdisp : |r - (k : ℝ)| ≤ 1 := by
    have hd := targetSlopeRightIndex_displacement U V M u v
    exact abs_le.mpr ⟨hd.1.le, hd.2.trans (by norm_num)⟩
  have hratio : (u : ℝ) / U ≤ 2 := (div_le_iff₀ hU).mpr hu.2
  have heq : M * (v : ℝ) / V - (k : ℝ) * (u : ℝ) / U =
      ((u : ℝ) / U) * (r - (k : ℝ)) := by
    dsimp [r]
    field_simp
  apply max_le
  · change |M * (v : ℝ) / V - (k : ℝ) * (u : ℝ) / U| ≤ 2
    calc
      |M * (v : ℝ) / V - (k : ℝ) * (u : ℝ) / U| =
          ((u : ℝ) / U) * |r - (k : ℝ)| := by rw [heq, abs_mul, abs_of_pos (div_pos hupos hU)]
      _ ≤ ((u : ℝ) / U) * 1 := mul_le_mul_of_nonneg_left hdisp (div_nonneg hupos.le hU.le)
      _ ≤ 2 := by simpa only [mul_one] using hratio
  · change |(u : ℝ) / U| ≤ 2
    simpa only [abs_of_pos (div_pos hupos hU)] using hratio

/-- The actual target vector `(v,u)` in an `Ico` dyadic box has normalized
sup norm at most two at its own right-ceiling target index. -/
theorem dyadicFactorBoxTargetRightIndex_supNorm_le_two
    {i : ℕ × ℕ × ℕ × ℕ} (M : ℕ)
    {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ dyadicBox i) :
    slopeVectorSupNorm ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ) (M : ℝ)
      (dyadicFactorBoxTargetRightIndex i M q : ℝ) ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ)) ≤ 2 := by
  apply targetSlopeRightIndex_supNorm_le_two_weak
    ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ) (M : ℝ)
    (by positivity) (by positivity)
  exact ⟨by exact_mod_cast (dyadicBox_coordinate_lower_bounds hq).2.2.1,
    by exact_mod_cast (dyadicBox_coordinate_upper_bounds hq).2.2.1⟩

/-- All nonempty actual source-cell / literal target-center incidences. -/
def dyadicSourceTargetCellPairs
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : Finset (ℕ × ℤ) := by
  classical
  exact ((activeDyadicSourceRatioIndices theta Y i M) ×ˢ targetSlopeIntegerCenters (M : ℝ)).filter
    fun p => ∃ q ∈ dyadicFactorBoxLocalRatioCell theta Y i M p.1,
      dyadicFactorBoxTargetRightIndex i M q = p.2

theorem mem_dyadicSourceTargetCellPairs
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (j : ℕ) (k : ℤ) :
    (j, k) ∈ dyadicSourceTargetCellPairs theta Y i M ↔
      j ∈ dyadicSourceIndicesForTargetIndex theta Y i M k ∧
        k ∈ targetSlopeIntegerCenters (M : ℝ) := by
  classical
  simp [dyadicSourceTargetCellPairs, dyadicSourceIndicesForTargetIndex,
    and_assoc, and_left_comm, and_comm]

/-- Every actual factor tuple belongs to a source cell whose pair with its
own target ceiling index is retained.  No source representative is used. -/
theorem exists_dyadicSourceTargetCellPair_covering
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ dyadicFactorBoxCell theta Y i) :
    ∃ p ∈ dyadicSourceTargetCellPairs theta Y i M,
      q ∈ dyadicFactorBoxLocalRatioCell theta Y i M p.1 ∧
        dyadicFactorBoxTargetRightIndex i M q = p.2 := by
  classical
  obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp
    (dyadicFactorBoxCell_subset_biUnion_localRatioCells theta Y i hM hq)
  have hjactive : j ∈ activeDyadicSourceRatioIndices theta Y i M :=
    Finset.mem_filter.mpr ⟨hj, ⟨q, hqj⟩⟩
  refine ⟨(j, dyadicFactorBoxTargetRightIndex i M q), ?_, hqj, rfl⟩
  apply (mem_dyadicSourceTargetCellPairs theta Y i M _ _).mpr
  exact ⟨Finset.mem_filter.mpr ⟨hjactive, q, hqj, rfl⟩,
    dyadicFactorBoxTargetRightIndex_mem_integerCenters hM (Finset.mem_inter.mp hq).2⟩

/-- A fixed-target pair fibre is exactly the already bounded actual source
incidence set, embedded as pairs. -/
theorem dyadicSourceTargetCellPairs_fiber
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (k : ℤ)
    (hk : k ∈ targetSlopeIntegerCenters (M : ℝ)) :
    (dyadicSourceTargetCellPairs theta Y i M).filter (fun p => p.2 = k) =
      (dyadicSourceIndicesForTargetIndex theta Y i M k).image (fun j => (j, k)) := by
  classical
  ext ⟨j, l⟩
  simp only [Finset.mem_filter, mem_dyadicSourceTargetCellPairs, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hj, _⟩, rfl⟩
    exact ⟨j, hj, rfl, rfl⟩
  · rintro ⟨j', hj', rfl, rfl⟩
    exact ⟨⟨hj', hk⟩, rfl⟩

/-- The actual pair fibre over any target integer has cardinality at most
337, with the geometric and arithmetic hypotheses discharged internally. -/
theorem card_dyadicSourceTargetCellPairs_fiber_le_337
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) (k : ℤ) :
    ((dyadicSourceTargetCellPairs theta Y i M).filter (fun p => p.2 = k)).card ≤ 337 := by
  classical
  by_cases hk : k ∈ targetSlopeIntegerCenters (M : ℝ)
  · rw [dyadicSourceTargetCellPairs_fiber theta Y i M k hk]
    exact Finset.card_image_le.trans (card_dyadicSourceIndicesForTargetIndex_le_337 theta Y i hM hscale k)
  · have hempty : (dyadicSourceTargetCellPairs theta Y i M).filter (fun p => p.2 = k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨j, l⟩ hp
      obtain ⟨hp, hl⟩ := Finset.mem_filter.mp hp
      exact hk (hl ▸ ((mem_dyadicSourceTargetCellPairs theta Y i M j l).mp hp).2)
    rw [hempty]
    simp

/-- Exact fibrewise summation over all actual cell pairs. -/
theorem sum_dyadicSourceTargetCellPairs_eq
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (w : ℤ → ℝ) :
    (∑ p ∈ dyadicSourceTargetCellPairs theta Y i M, w p.2) =
      ∑ k ∈ targetSlopeIntegerCenters (M : ℝ),
        ((dyadicSourceIndicesForTargetIndex theta Y i M k).card : ℝ) * w k := by
  classical
  unfold dyadicSourceTargetCellPairs
  rw [Finset.sum_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter]
  simp [dyadicSourceIndicesForTargetIndex]

/-- Reverse multiplicity transfers any nonnegative target weight to the
entire actual pair set, without limiting targets per source. -/
theorem sum_dyadicSourceTargetCellPairs_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (w : ℤ → ℝ) (hw : ∀ k ∈ targetSlopeIntegerCenters (M : ℝ), 0 ≤ w k) :
    (∑ p ∈ dyadicSourceTargetCellPairs theta Y i M, w p.2) ≤
      337 * ∑ k ∈ targetSlopeIntegerCenters (M : ℝ), w k := by
  rw [sum_dyadicSourceTargetCellPairs_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_dyadicSourceIndicesForTargetIndex_le_337 theta Y i hM hscale k) (hw k hk)

/-- The complete actual cell-pair cover contains at most `1348M` pairs.
This follows from reverse multiplicity, not from targets per source. -/
theorem card_dyadicSourceTargetCellPairs_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) :
    (dyadicSourceTargetCellPairs theta Y i M).card ≤ 1348 * M := by
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpack := card_le_one_add_div_of_separated_real_centers
    (targetSlopeIntegerCenters (M : ℝ)) (fun k : ℤ => (k : ℝ)) 0 (3 * (M : ℝ)) 1
    (by norm_num) (by positivity)
    (fun k hk => ⟨by have h := (targetSlopeIntegerCenters_range (M : ℝ) hk).1; linarith,
      (targetSlopeIntegerCenters_range (M : ℝ) hk).2⟩)
    (targetSlopeIntegerCenters_separated (M : ℝ))
  have hcard : ((targetSlopeIntegerCenters (M : ℝ)).card : ℝ) ≤ 4 * (M : ℝ) := by
    norm_num at hpack
    linarith
  have htransport := sum_dyadicSourceTargetCellPairs_le theta Y i hM hscale (fun _ => 1)
    (by intro k hk; norm_num)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at htransport
  have hfinal : ((dyadicSourceTargetCellPairs theta Y i M).card : ℝ) ≤ 1348 * (M : ℝ) := by
    linarith
  exact_mod_cast hfinal

/-- The full actual source/target pair cover has reciprocal-first-minimum
weight at most `337 * 64` times the proved target-lattice scale. -/
theorem sum_reciprocalFirstSlopeSupNorm_dyadicSourceTargetCellPairs_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) :
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    (∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
      reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) ≤
      21568 * (Real.sqrt (U * V * (M : ℝ)) + U + V) *
        (1 + Real.log (1 + U / Real.sqrt (U * V / (M : ℝ)))) := by
  dsimp only
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have htransport := sum_dyadicSourceTargetCellPairs_le theta Y i hM hscale
    (fun k => reciprocalFirstSlopeSupNorm U V (M : ℝ) (k : ℝ))
    (fun k _ => (reciprocalFirstSlopeSupNorm_pos U V (M : ℝ) (k : ℝ) hU hV hMpos).le)
  have htarget := sum_reciprocalFirstSlopeSupNorm_integerCenters_le U V (M : ℝ) hU hV hMone
  calc
    _ ≤ 337 * ∑ k ∈ targetSlopeIntegerCenters (M : ℝ),
        reciprocalFirstSlopeSupNorm U V (M : ℝ) (k : ℝ) := htransport
    _ ≤ 337 * (64 * (Real.sqrt (U * V * (M : ℝ)) + U + V) *
        (1 + Real.log (1 + U / Real.sqrt (U * V / (M : ℝ))))) :=
      mul_le_mul_of_nonneg_left htarget (by norm_num)
    _ = _ := by ring

end

end PellPaper
