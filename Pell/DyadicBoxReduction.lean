import Mathlib.Data.Nat.Log
import Pell.DyadicCountingReduction

/-!
# Dyadic boxes for the separated factor tuples

The determinant argument in the manuscript eventually counts the tuples in
`dyadicFactorTuples` after putting each positive coordinate into a dyadic
interval.  This file carries out only that finite combinatorial reduction.
It neither estimates an individual box nor asserts a power saving.

The index range has the natural logarithmic size: a coordinate bounded by
`H` is assigned the index `Nat.log 2 n`, which lies below
`Nat.clog 2 (H + 1)`.
-/

namespace PellPaper

/-- The half-open dyadic interval `[2^k, 2^(k+1))` in the natural numbers. -/
def dyadicInterval (k : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ k) (2 ^ (k + 1))

/-- The number of dyadic scales needed for positive naturals at most `H`. -/
def dyadicScaleCount (H : ℕ) : ℕ :=
  Nat.clog 2 (H + 1)

/-- A four-coordinate dyadic box, with one dyadic interval per coordinate. -/
def dyadicBox (i : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (dyadicInterval i.1).product
    ((dyadicInterval i.2.1).product
      ((dyadicInterval i.2.2.1).product (dyadicInterval i.2.2.2)))

/-- The finite family of boxes needed for four coordinates with the displayed
individual upper bounds. -/
def dyadicBoxIndices (Hd He Hu Hv : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (dyadicScaleCount Hd)).product
    ((Finset.range (dyadicScaleCount He)).product
      ((Finset.range (dyadicScaleCount Hu)).product
        (Finset.range (dyadicScaleCount Hv))))

/-- The finite union of all coordinate dyadic boxes at the given bounds. -/
def dyadicBoxUnion (Hd He Hu Hv : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (dyadicBoxIndices Hd He Hu Hv).biUnion dyadicBox

/-- A positive natural lies in the dyadic interval indexed by its binary
floor logarithm. -/
theorem mem_dyadicInterval_log {n : ℕ} (hn : 0 < n) :
    n ∈ dyadicInterval (Nat.log 2 n) := by
  refine Finset.mem_Ico.mpr ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hn), ?_⟩
  simpa [Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self Nat.one_lt_two n

/-- The binary floor logarithm of a positive `n ≤ H` is one of the finitely
many scale indices required at height `H`. -/
theorem log_mem_dyadicScaleRange {n H : ℕ} (hn : 0 < n) (hH : n ≤ H) :
    Nat.log 2 n ∈ Finset.range (dyadicScaleCount H) := by
  apply Finset.mem_range.mpr
  rw [dyadicScaleCount, Nat.lt_clog_iff_pow_lt Nat.one_lt_two]
  exact (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)).trans_lt
    (by simpa [Nat.succ_eq_add_one] using Nat.lt_succ_of_le hH)

/-- A positive coordinate tuple belongs to its explicitly chosen dyadic box. -/
theorem mem_dyadicBox_of_pos
    {d e u v : ℕ}
    (hd : 0 < d) (he : 0 < e) (hu : 0 < u) (hv : 0 < v) :
    (d, e, u, v) ∈ dyadicBox
      (Nat.log 2 d, Nat.log 2 e, Nat.log 2 u, Nat.log 2 v) := by
  refine Finset.mem_product.mpr ⟨mem_dyadicInterval_log hd, ?_⟩
  refine Finset.mem_product.mpr ⟨mem_dyadicInterval_log he, ?_⟩
  exact Finset.mem_product.mpr
    ⟨mem_dyadicInterval_log hu, mem_dyadicInterval_log hv⟩

/-- The chosen dyadic box index is in the finite index family at the stated
coordinate bounds. -/
theorem log_tuple_mem_dyadicBoxIndices
    {d e u v Hd He Hu Hv : ℕ}
    (hd : 0 < d) (he : 0 < e) (hu : 0 < u) (hv : 0 < v)
    (hdH : d ≤ Hd) (heH : e ≤ He) (huH : u ≤ Hu) (hvH : v ≤ Hv) :
    (Nat.log 2 d, Nat.log 2 e, Nat.log 2 u, Nat.log 2 v) ∈
      dyadicBoxIndices Hd He Hu Hv := by
  refine Finset.mem_product.mpr ⟨log_mem_dyadicScaleRange hd hdH, ?_⟩
  refine Finset.mem_product.mpr ⟨log_mem_dyadicScaleRange he heH, ?_⟩
  exact Finset.mem_product.mpr
    ⟨log_mem_dyadicScaleRange hu huH, log_mem_dyadicScaleRange hv hvH⟩

/-- Every positive tuple within the four coordinate bounds belongs to the
finite union of the corresponding dyadic boxes. -/
theorem mem_dyadicBoxUnion_of_pos_le
    {d e u v Hd He Hu Hv : ℕ}
    (hd : 0 < d) (he : 0 < e) (hu : 0 < u) (hv : 0 < v)
    (hdH : d ≤ Hd) (heH : e ≤ He) (huH : u ≤ Hu) (hvH : v ≤ Hv) :
    (d, e, u, v) ∈ dyadicBoxUnion Hd He Hu Hv := by
  apply Finset.mem_biUnion.mpr
  exact ⟨(Nat.log 2 d, Nat.log 2 e, Nat.log 2 u, Nat.log 2 v),
    log_tuple_mem_dyadicBoxIndices hd he hu hv hdH heH huH hvH,
    mem_dyadicBox_of_pos hd he hu hv⟩

/-- The number of boxes is the product of the four binary scale counts. -/
@[simp] theorem card_dyadicBoxIndices (Hd He Hu Hv : ℕ) :
    (dyadicBoxIndices Hd He Hu Hv).card =
      dyadicScaleCount Hd *
        (dyadicScaleCount He * (dyadicScaleCount Hu * dyadicScaleCount Hv)) := by
  simp [dyadicBoxIndices]

/-- A finite set of positive bounded tuples is no larger than the sum of its
intersections with the dyadic boxes.  This is just finite-union
subadditivity; it is the point at which future boxwise determinant estimates
can be inserted. -/
theorem card_le_sum_card_inter_dyadicBoxes
    {S : Finset (ℕ × ℕ × ℕ × ℕ)} {Hd He Hu Hv : ℕ}
    (hS : ∀ p ∈ S,
      0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2 ∧
      p.1 ≤ Hd ∧ p.2.1 ≤ He ∧ p.2.2.1 ≤ Hu ∧ p.2.2.2 ≤ Hv) :
    S.card ≤ ∑ i ∈ dyadicBoxIndices Hd He Hu Hv,
      (S ∩ dyadicBox i).card := by
  have hsubset : S ⊆ (dyadicBoxIndices Hd He Hu Hv).biUnion
      (fun i => S ∩ dyadicBox i) := by
    intro p hp
    rcases hS p hp with ⟨hd, he, hu, hv, hdH, heH, huH, hvH⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨(Nat.log 2 p.1, Nat.log 2 p.2.1, Nat.log 2 p.2.2.1,
      Nat.log 2 p.2.2.2),
      log_tuple_mem_dyadicBoxIndices hd he hu hv hdH heH huH hvH,
      Finset.mem_inter.mpr ⟨hp,
        mem_dyadicBox_of_pos hd he hu hv⟩⟩
  exact (Finset.card_le_card hsubset).trans Finset.card_biUnion_le

/-- The index family appropriate for the bounded separated factor tuples.
The two square coordinates have height `dyadicFactorHeight θ Y`, while the
two squarefree coordinates are below `2Y`. -/
noncomputable def dyadicFactorBoxIndices (θ : ℝ) (Y : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  dyadicBoxIndices (dyadicFactorHeight θ Y) (dyadicFactorHeight θ Y) (2 * Y) (2 * Y)

/-- Every separated factor tuple lies in the finite union of its coordinate
dyadic boxes. -/
theorem dyadicFactorTuples_subset_dyadicBoxUnion (θ : ℝ) (Y : ℕ) :
    dyadicFactorTuples θ Y ⊆
      dyadicBoxUnion (dyadicFactorHeight θ Y) (dyadicFactorHeight θ Y) (2 * Y) (2 * Y) := by
  intro p hp
  obtain ⟨hd, he, hu, hv, hdH, heH, huH, hvH, _⟩ :=
    mem_dyadicFactorTuples.mp hp
  exact mem_dyadicBoxUnion_of_pos_le hd he hu hv hdH heH
    (Nat.le_of_lt huH) (Nat.le_of_lt hvH)

/-- The actual finite dyadic box reduction for the tuples produced from
squarefree Pell exceptions. -/
theorem dyadicFactorTuples_card_le_dyadicBox_sum (θ : ℝ) (Y : ℕ) :
    (dyadicFactorTuples θ Y).card ≤
      ∑ i ∈ dyadicFactorBoxIndices θ Y,
        ((dyadicFactorTuples θ Y) ∩ dyadicBox i).card := by
  apply card_le_sum_card_inter_dyadicBoxes
  intro p hp
  obtain ⟨hd, he, hu, hv, hdH, heH, huH, hvH, _⟩ :=
    mem_dyadicFactorTuples.mp hp
  exact ⟨hd, he, hu, hv, hdH, heH, Nat.le_of_lt huH, Nat.le_of_lt hvH⟩

end PellPaper
