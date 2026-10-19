import Pell.DyadicFactorScaleComparability
import Pell.FiniteCellSparsity

/-!
# Explicit multiplicative source-ratio covers of dyadic factor boxes

A raw dyadic box need not have one sufficiently short source-ratio window.
This file partitions its source-ratio range into at most `2M` explicit
multiplicative cells, each of relative width `1 + 1/M`.  The construction is
finite and literal; no determinant estimate, choice of analytic parameters,
or point count is asserted.
-/

namespace PellPaper

noncomputable section

/-- The multiplicative mesh step for an integral localization parameter. -/
def localRatioMeshStep (M : ℕ) : ℝ := 1 + 1 / (M : ℝ)

/-- The left end of the source-ratio range of a dyadic box. -/
def dyadicFactorBoxLocalRatioStart (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ((2 ^ i.1 : ℕ) : ℝ) / (2 * ((2 ^ i.2.1 : ℕ) : ℝ))

/-- The `k`th multiplicative source-ratio centre in a dyadic box. -/
def dyadicFactorBoxLocalRatioCenter (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ) : ℝ :=
  dyadicFactorBoxLocalRatioStart i * localRatioMeshStep M ^ k

/-- The portion of a dyadic factor box whose source ratio lies in its `k`th
explicit multiplicative localization window. -/
noncomputable def dyadicFactorBoxLocalRatioCell
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  (dyadicFactorBoxCell theta Y i).filter fun q =>
    dyadicFactorBoxLocalRatioCenter i M k ≤ (q.1 : ℝ) / (q.2.1 : ℝ) ∧
      (q.1 : ℝ) / (q.2.1 : ℝ) ≤
        dyadicFactorBoxLocalRatioCenter i M k * localRatioMeshStep M

theorem dyadicFactorBoxLocalRatioStart_pos (i : ℕ × ℕ × ℕ × ℕ) :
    0 < dyadicFactorBoxLocalRatioStart i := by
  unfold dyadicFactorBoxLocalRatioStart
  positivity

/-- The source ratio of a tuple in a dyadic box lies between the displayed
left end and four times that end. -/
theorem dyadicBox_sourceRatio_between_localRatioStart_and_four_mul
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ}
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    dyadicFactorBoxLocalRatioStart i ≤ (d : ℝ) / (e : ℝ) ∧
      (d : ℝ) / (e : ℝ) ≤ 4 * dyadicFactorBoxLocalRatioStart i := by
  have hlower := dyadicBox_coordinate_lower_bounds hbox
  have hupper := dyadicBox_coordinate_upper_bounds hbox
  have hDpos : 0 < ((2 ^ i.1 : ℕ) : ℝ) := by positivity
  have hEpos : 0 < ((2 ^ i.2.1 : ℕ) : ℝ) := by positivity
  have hdpos : 0 < (d : ℝ) := by
    exact lt_of_lt_of_le hDpos (by exact_mod_cast hlower.1)
  have hepos : 0 < (e : ℝ) := by
    exact lt_of_lt_of_le hEpos (by exact_mod_cast hlower.2.1)
  have hDle : ((2 ^ i.1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hlower.1
  have hEle : ((2 ^ i.2.1 : ℕ) : ℝ) ≤ (e : ℝ) := by exact_mod_cast hlower.2.1
  have hdle : (d : ℝ) ≤ 2 * ((2 ^ i.1 : ℕ) : ℝ) := by exact_mod_cast hupper.1
  have hele : (e : ℝ) ≤ 2 * ((2 ^ i.2.1 : ℕ) : ℝ) := by exact_mod_cast hupper.2.1
  constructor
  · unfold dyadicFactorBoxLocalRatioStart
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hEpos) hepos).mpr
    calc
      ((2 ^ i.1 : ℕ) : ℝ) * (e : ℝ) ≤ (d : ℝ) * (e : ℝ) :=
        mul_le_mul_of_nonneg_right hDle hepos.le
      _ ≤ (d : ℝ) * (2 * ((2 ^ i.2.1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hele hdpos.le
  · have hratio : (d : ℝ) / (e : ℝ) ≤
        (2 * ((2 ^ i.1 : ℕ) : ℝ)) / ((2 ^ i.2.1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hepos hEpos).mpr
      calc
        (d : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
            (2 * ((2 ^ i.1 : ℕ) : ℝ)) * ((2 ^ i.2.1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdle hEpos.le
        _ ≤ (2 * ((2 ^ i.1 : ℕ) : ℝ)) * (e : ℝ) :=
          mul_le_mul_of_nonneg_left hEle (by positivity)
    calc
      (d : ℝ) / (e : ℝ) ≤
          (2 * ((2 ^ i.1 : ℕ) : ℝ)) / ((2 ^ i.2.1 : ℕ) : ℝ) := hratio
      _ = 4 * dyadicFactorBoxLocalRatioStart i := by
        unfold dyadicFactorBoxLocalRatioStart
        field_simp [hEpos.ne']
        norm_num

/-- Membership in a local-ratio cell retains the ambient dyadic factor box
and provides its literal common multiplicative source window. -/
theorem mem_dyadicFactorBoxLocalRatioCell
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {M k : ℕ}
    {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ dyadicFactorBoxLocalRatioCell theta Y i M k) :
    q ∈ dyadicFactorBoxCell theta Y i ∧
      dyadicFactorBoxLocalRatioCenter i M k ≤ (q.1 : ℝ) / (q.2.1 : ℝ) ∧
        (q.1 : ℝ) / (q.2.1 : ℝ) ≤
          dyadicFactorBoxLocalRatioCenter i M k * localRatioMeshStep M := by
  exact Finset.mem_filter.mp hq

/-- Each displayed local-ratio cell is a literal subcell of its ambient
dyadic factor box. -/
theorem dyadicFactorBoxLocalRatioCell_subset_dyadicFactorBoxCell
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ) :
    dyadicFactorBoxLocalRatioCell theta Y i M k ⊆
      dyadicFactorBoxCell theta Y i := by
  intro q hq
  exact (mem_dyadicFactorBoxLocalRatioCell hq).1

/-- The exact common source-ratio window of a local-ratio cell, in the
real-parameter shape consumed by the determinant endpoint. -/
theorem dyadicFactorBoxLocalRatioCell_commonWindow
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {M k : ℕ}
    {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ dyadicFactorBoxLocalRatioCell theta Y i M k) :
    dyadicFactorBoxLocalRatioCenter i M k ≤ (q.1 : ℝ) / (q.2.1 : ℝ) ∧
      (q.1 : ℝ) / (q.2.1 : ℝ) ≤
        dyadicFactorBoxLocalRatioCenter i M k * (1 + 1 / (M : ℝ)) := by
  simpa [localRatioMeshStep] using (mem_dyadicFactorBoxLocalRatioCell hq).2

theorem localRatioMeshStep_pow_ge_two {M : ℕ} (hM : 0 < M) :
    2 ≤ localRatioMeshStep M ^ M := by
  unfold localRatioMeshStep
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hinvnonneg : 0 ≤ 1 / (M : ℝ) := by positivity
  have hbound := one_add_mul_le_pow (a := 1 / (M : ℝ)) (by linarith) M
  norm_num [hM0] at hbound ⊢
  exact hbound

theorem localRatioMeshStep_pow_two_mul_ge_four {M : ℕ} (hM : 0 < M) :
    4 ≤ localRatioMeshStep M ^ (2 * M) := by
  have htwo := localRatioMeshStep_pow_ge_two hM
  have hnonneg : 0 ≤ localRatioMeshStep M ^ M := by
    apply pow_nonneg
    unfold localRatioMeshStep
    positivity
  have hsq : 4 ≤ localRatioMeshStep M ^ M * localRatioMeshStep M ^ M := by
    nlinarith [sq_nonneg (localRatioMeshStep M ^ M - 2)]
  rw [show 2 * M = M + M by omega, pow_add]
  exact hsq

/-- Every ratio in `[s,4s]` belongs to one of the first `2M` multiplicative
windows of relative width `1 + 1/M`. -/
theorem exists_localRatioMeshInterval_index_of_between
    {M : ℕ} (hM : 0 < M) {s x : ℝ} (hs : 0 < s)
    (hlower : s ≤ x) (hupper : x ≤ 4 * s) :
    ∃ k : ℕ, k < 2 * M ∧
      s * localRatioMeshStep M ^ k ≤ x ∧
        x ≤ (s * localRatioMeshStep M ^ k) * localRatioMeshStep M := by
  classical
  let t : ℝ := localRatioMeshStep M
  have htpos : 0 < t := by
    unfold t localRatioMeshStep
    positivity
  have htone : 1 ≤ t := by
    unfold t localRatioMeshStep
    have : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith
  have hpow : 4 ≤ t ^ (2 * M) := by
    simpa [t] using localRatioMeshStep_pow_two_mul_ge_four hM
  have hendpoint : x ≤ s * t ^ (2 * M) := by
    calc
      x ≤ 4 * s := hupper
      _ = s * 4 := by ring
      _ ≤ s * t ^ (2 * M) := mul_le_mul_of_nonneg_left hpow hs.le
  let P : ℕ → Prop := fun n => x ≤ s * t ^ n
  have hP : ∃ n, P n := ⟨2 * M, hendpoint⟩
  have hn : P (Nat.find hP) := Nat.find_spec hP
  have hnle : Nat.find hP ≤ 2 * M := Nat.find_min' hP hendpoint
  by_cases hnzero : Nat.find hP = 0
  · refine ⟨0, Nat.mul_pos (by norm_num) hM, ?_, ?_⟩
    · simpa [t] using hlower
    · calc
        x ≤ s := by simpa [P, hnzero] using hn
        _ = s * 1 := by ring
        _ ≤ s * t := mul_le_mul_of_nonneg_left htone hs.le
        _ = (s * localRatioMeshStep M ^ 0) * localRatioMeshStep M := by simp [t]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnzero
    refine ⟨k, ?_, ?_, ?_⟩
    · rw [hk] at hnle
      omega
    · by_contra hnot
      have hxlt : x < s * t ^ k := lt_of_not_ge hnot
      have hPprev : P k := le_of_lt hxlt
      have hmin := Nat.find_min' hP hPprev
      rw [hk] at hmin
      omega
    · have hns : x ≤ s * t ^ Nat.succ k := by
        simpa [P, hk] using hn
      calc
        x ≤ s * t ^ Nat.succ k := hns
        _ = (s * t ^ k) * t := by rw [pow_succ]; ring
        _ = (s * localRatioMeshStep M ^ k) * localRatioMeshStep M := by simp [t]

/-- A dyadic factor box is covered by at most `2M` explicit multiplicative
source-ratio cells.  Each cell has width `1 + 1/M`; this is only the local
covering step and makes no determinant or counting assertion. -/
theorem dyadicFactorBoxCell_subset_biUnion_localRatioCells
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) :
    dyadicFactorBoxCell theta Y i ⊆
      (Finset.range (2 * M)).biUnion
        (dyadicFactorBoxLocalRatioCell theta Y i M) := by
  intro q hq
  have hbox : (q.1, q.2.1, q.2.2.1, q.2.2.2) ∈ dyadicBox i := by
    exact (Finset.mem_inter.mp hq).2
  have hratio := dyadicBox_sourceRatio_between_localRatioStart_and_four_mul hbox
  obtain ⟨k, hk, hklower, hkupper⟩ :=
    exists_localRatioMeshInterval_index_of_between hM
      (dyadicFactorBoxLocalRatioStart_pos i) hratio.1 hratio.2
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hq, ?_⟩
  constructor
  · simpa [dyadicFactorBoxLocalRatioCenter] using hklower
  · simpa [dyadicFactorBoxLocalRatioCenter] using hkupper

/-- The finite local cover gives the corresponding elementary sum of
subcell-cardinality upper bound.  It is only finite-union subadditivity, not
a determinant or curve-point estimate. -/
theorem card_dyadicFactorBoxCell_le_sum_card_localRatioCells
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) :
    (dyadicFactorBoxCell theta Y i).card ≤
      ∑ k ∈ Finset.range (2 * M),
        (dyadicFactorBoxLocalRatioCell theta Y i M k).card := by
  exact (Finset.card_le_card
    (dyadicFactorBoxCell_subset_biUnion_localRatioCells theta Y i hM)).trans
      Finset.card_biUnion_le

end

end PellPaper
