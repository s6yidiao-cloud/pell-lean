import Pell.ExceptionalDecomposition
import Pell.FixedHeight

/-!
# Square-part reduction on a dyadic exceptional family

This module isolates the finite square-part bookkeeping needed to pass from
arbitrary exceptional Pell radicands in a dyadic interval to squarefree
radicands.  The transferred unit bound deliberately retains the original
radicand `s ^ 2 * w`; it does not claim the stronger, generally false bound
`epsilon_w ≤ w ^ θ`.

No determinant, divisor, or power-saving estimate is used here.
-/

namespace PellPaper

/-- The exceptional Pell radicands in the half-open dyadic interval
`[Y, 2Y)`, without imposing squarefreeness. -/
noncomputable def dyadicSquarePartExceptionalSet (θ : ℝ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico Y (2 * Y)).filter (SmallFundamentalSolution θ)

/-- The cardinality of the dyadic exceptional family before square-part
decomposition. -/
noncomputable def dyadicSquarePartExceptionalCount (θ : ℝ) (Y : ℕ) : ℕ :=
  (dyadicSquarePartExceptionalSet θ Y).card

/-- Membership in the dyadic exceptional family. -/
@[simp] theorem mem_dyadicSquarePartExceptionalSet {θ : ℝ} {Y m : ℕ} :
    m ∈ dyadicSquarePartExceptionalSet θ Y ↔
      Y ≤ m ∧ m < 2 * Y ∧ SmallFundamentalSolution θ m := by
  classical
  simp [dyadicSquarePartExceptionalSet, and_assoc]

/-- A member of the dyadic family is also a global exception at the closed
cutoff `2Y`. -/
theorem mem_exceptionalSet_two_mul_of_mem_dyadicSquarePartExceptionalSet
    {θ : ℝ} {Y m : ℕ} (hm : m ∈ dyadicSquarePartExceptionalSet θ Y) :
    m ∈ exceptionalSet θ (2 * Y) := by
  obtain ⟨_, hmhi, hsmall⟩ := mem_dyadicSquarePartExceptionalSet.mp hm
  obtain ⟨hmpos, _⟩ := positive_nonsquare_of_smallFundamentalSolution hsmall
  exact mem_exceptionalSet.mpr ⟨hmpos, Nat.le_of_lt hmhi, hsmall⟩

/-- Every dyadic exception has the positive square/squarefree decomposition,
with fundamental solutions on both radicands and the transferred unit bound.
The two dyadic inequalities are retained explicitly. -/
theorem exists_dyadic_square_part_fundamental_data_of_mem
    {θ : ℝ} {Y m : ℕ} (hm : m ∈ dyadicSquarePartExceptionalSet θ Y) :
    ∃ s w : ℕ,
      0 < s ∧ 1 < w ∧ Y ≤ m ∧ m < 2 * Y ∧ m = s ^ 2 * w ∧
        Squarefree w ∧ ¬ IsSquare w ∧
          ∃ a : Pell.Solution₁ (w : ℤ), ∃ b : Pell.Solution₁ (m : ℤ),
            Pell.IsFundamental a ∧ Pell.IsFundamental b ∧
              epsilon a ≤ epsilon b ∧ epsilon b ≤ (m : ℝ) ^ θ := by
  obtain ⟨hmlo, hmhi, hsmall⟩ := mem_dyadicSquarePartExceptionalSet.mp hm
  obtain ⟨s, w, hs, hw, hdecomp, hsf, hwns, a, b, ha, hb, hab, hbsmall⟩ :=
    exists_square_part_fundamental_data_of_smallFundamentalSolution hsmall
  exact ⟨s, w, hs, hw, hmlo, hmhi, hdecomp, hsf, hwns,
    a, b, ha, hb, hab, hbsmall⟩

/-- The dyadic bounds on a square-part decomposition give the exact integral
interval for its squarefree factor.  The upper endpoint is closed because the
original dyadic interval is half-open. -/
theorem dyadic_squarefree_factor_div_bounds {Y m s w : ℕ}
    (hs : 0 < s) (hdecomp : m = s ^ 2 * w)
    (hmlo : Y ≤ m) (hmhi : m < 2 * Y) :
    Y / s ^ 2 ≤ w ∧ w ≤ (2 * Y - 1) / s ^ 2 := by
  have hsqpos : 0 < s ^ 2 := pow_pos hs 2
  have hprodlo : Y ≤ s ^ 2 * w := by simpa [hdecomp] using hmlo
  have hprodhi : s ^ 2 * w < 2 * Y := by simpa [hdecomp] using hmhi
  constructor
  · exact Nat.div_le_of_le_mul hprodlo
  · apply (Nat.le_div_iff_mul_le hsqpos).mpr
    have hle : s ^ 2 * w ≤ 2 * Y - 1 := by omega
    simpa [Nat.mul_comm] using hle

/-- The square-part root of a dyadic exception lies in the finite interval
`[1, 2Y)`. -/
theorem square_part_root_lt_two_mul_scale {Y m s w : ℕ}
    (hs : 0 < s) (hw : 1 < w) (hdecomp : m = s ^ 2 * w)
    (hmhi : m < 2 * Y) : s < 2 * Y := by
  have hsone : 1 ≤ s := by omega
  have hwpos : 0 < w := lt_trans Nat.zero_lt_one hw
  have hsle : s ≤ s ^ 2 * w := by
    calc
      s = s * 1 := by simp
      _ ≤ s * s := Nat.mul_le_mul_left s hsone
      _ = s ^ 2 := by ring
      _ ≤ s ^ 2 * w := Nat.le_mul_of_pos_right _ hwpos
  have hsm : s ≤ m := by simpa [hdecomp] using hsle
  exact hsm.trans_lt hmhi

/-- The squarefree factor of a dyadic exception is itself below `2Y`. -/
theorem squarefree_factor_lt_two_mul_scale {Y m s w : ℕ}
    (hs : 0 < s) (hdecomp : m = s ^ 2 * w)
    (hmhi : m < 2 * Y) : w < 2 * Y := by
  have hsqpos : 0 < s ^ 2 := pow_pos hs 2
  have hwm : w ≤ m := by
    rw [hdecomp]
    exact Nat.le_mul_of_pos_left w hsqpos
  exact hwm.trans_lt hmhi

/-- For a fixed square-part root, the finite squarefree family resulting from
the dyadic reduction.  The unit bound is at the exact radicand
`s ^ 2 * w`, rather than at `w`. -/
noncomputable def dyadicTransferredSquarefreeSet (θ : ℝ) (Y s : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.Ico 2 (2 * Y)).filter fun w ↦
    Y ≤ s ^ 2 * w ∧ s ^ 2 * w < 2 * Y ∧ Squarefree w ∧
      ∃ a : Pell.Solution₁ (w : ℤ),
        Pell.IsFundamental a ∧ epsilon a ≤ ((s ^ 2 * w : ℕ) : ℝ) ^ θ

/-- Membership in a fixed square-part transferred family. -/
@[simp] theorem mem_dyadicTransferredSquarefreeSet {θ : ℝ} {Y s w : ℕ} :
    w ∈ dyadicTransferredSquarefreeSet θ Y s ↔
      2 ≤ w ∧ w < 2 * Y ∧ Y ≤ s ^ 2 * w ∧ s ^ 2 * w < 2 * Y ∧
        Squarefree w ∧ ∃ a : Pell.Solution₁ (w : ℤ),
          Pell.IsFundamental a ∧ epsilon a ≤ ((s ^ 2 * w : ℕ) : ℝ) ^ θ := by
  classical
  simp [dyadicTransferredSquarefreeSet, and_assoc]

/-- A square/squarefree decomposition of a dyadic exception places its
squarefree factor in the corresponding fixed-root transferred family. -/
theorem mem_dyadicTransferredSquarefreeSet_of_mem_dyadicSquarePartExceptionalSet
    {θ : ℝ} {Y m s w : ℕ} (hm : m ∈ dyadicSquarePartExceptionalSet θ Y)
    (hs : 0 < s) (hdecomp : m = s ^ 2 * w) (hsf : Squarefree w) :
    w ∈ dyadicTransferredSquarefreeSet θ Y s := by
  obtain ⟨hmlo, hmhi, hsmall⟩ := mem_dyadicSquarePartExceptionalSet.mp hm
  obtain ⟨hmpos, hmns⟩ := positive_nonsquare_of_smallFundamentalSolution hsmall
  have hwpos : 0 < w := by
    by_contra hwpos
    have hwzero : w = 0 := Nat.eq_zero_of_not_pos hwpos
    simp [hwzero] at hdecomp
    omega
  have hwns : ¬ IsSquare w := squarefree_part_not_isSquare hdecomp hmns
  have hwone : w ≠ 1 := fun hwone => hwns (hwone.symm ▸ IsSquare.one)
  have hwlower : 2 ≤ w := by omega
  have hwupper : w < 2 * Y :=
    squarefree_factor_lt_two_mul_scale hs hdecomp hmhi
  have hwpos_int : 0 < (w : ℤ) := by exact_mod_cast hwpos
  have hwns_int : ¬ IsSquare (w : ℤ) := by
    simpa only [Int.isSquare_natCast_iff] using hwns
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hwpos_int hwns_int
  have hmglobal : m ∈ exceptionalSet θ (2 * Y) :=
    mem_exceptionalSet_two_mul_of_mem_dyadicSquarePartExceptionalSet hm
  have hunit : epsilon a ≤ (m : ℝ) ^ θ :=
    epsilon_le_rpow_of_square_part_of_mem_exceptionalSet hmglobal hs hdecomp ha
  have hunit' : epsilon a ≤ ((s ^ 2 * w : ℕ) : ℝ) ^ θ := by
    simpa [hdecomp] using hunit
  exact mem_dyadicTransferredSquarefreeSet.mpr
    ⟨hwlower, hwupper, by simpa [hdecomp] using hmlo,
      by simpa [hdecomp] using hmhi, hsf, a, ha, hunit'⟩

/-- Every dyadic exception is the image of one of the finite transferred
squarefree families. -/
theorem dyadicSquarePartExceptionalSet_subset_transferred_union (θ : ℝ) (Y : ℕ) :
    dyadicSquarePartExceptionalSet θ Y ⊆
      (Finset.Ico 1 (2 * Y)).biUnion fun s ↦
        (dyadicTransferredSquarefreeSet θ Y s).image fun w ↦ s ^ 2 * w := by
  classical
  intro m hm
  obtain ⟨s, w, hs, hw, _, hmhi, hdecomp, hsf, _, _, _, _, _, _, _⟩ :=
    exists_dyadic_square_part_fundamental_data_of_mem hm
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_Ico.mpr ⟨by omega,
    square_part_root_lt_two_mul_scale hs hw hdecomp hmhi⟩, ?_⟩
  exact Finset.mem_image.mpr
    ⟨w, mem_dyadicTransferredSquarefreeSet_of_mem_dyadicSquarePartExceptionalSet
      hm hs hdecomp hsf, hdecomp.symm⟩

/-- The finite counting reduction for the complete dyadic exceptional family.
This is only a sum of finite transferred squarefree counts; no estimate for
an individual summand is asserted. -/
theorem dyadicSquarePartExceptionalCount_le_sum_transferred (θ : ℝ) (Y : ℕ) :
    dyadicSquarePartExceptionalCount θ Y ≤
      ∑ s ∈ Finset.Ico 1 (2 * Y), (dyadicTransferredSquarefreeSet θ Y s).card := by
  classical
  calc
    dyadicSquarePartExceptionalCount θ Y ≤
        ((Finset.Ico 1 (2 * Y)).biUnion fun s ↦
          (dyadicTransferredSquarefreeSet θ Y s).image fun w ↦ s ^ 2 * w).card :=
      Finset.card_le_card
        (dyadicSquarePartExceptionalSet_subset_transferred_union θ Y)
    _ ≤ ∑ s ∈ Finset.Ico 1 (2 * Y),
        ((dyadicTransferredSquarefreeSet θ Y s).image fun w ↦ s ^ 2 * w).card :=
      Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le

/-- The small square-part subfamily inside a dyadic exceptional interval. -/
noncomputable def dyadicSmallSquarePartExceptionalSet (θ : ℝ) (Y S : ℕ) :
    Finset ℕ := by
  classical
  exact (dyadicSquarePartExceptionalSet θ Y).filter fun m ↦
    ∃ s w : ℕ, 0 < s ∧ s < S ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w

/-- The large square-part subfamily inside a dyadic exceptional interval. -/
noncomputable def dyadicLargeSquarePartExceptionalSet (θ : ℝ) (Y S : ℕ) :
    Finset ℕ := by
  classical
  exact (dyadicSquarePartExceptionalSet θ Y).filter fun m ↦
    ∃ s w : ℕ, 0 < s ∧ S ≤ s ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w

@[simp] theorem mem_dyadicSmallSquarePartExceptionalSet {θ : ℝ} {Y S m : ℕ} :
    m ∈ dyadicSmallSquarePartExceptionalSet θ Y S ↔
      m ∈ dyadicSquarePartExceptionalSet θ Y ∧
        ∃ s w : ℕ, 0 < s ∧ s < S ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w := by
  classical
  simp [dyadicSmallSquarePartExceptionalSet]

@[simp] theorem mem_dyadicLargeSquarePartExceptionalSet {θ : ℝ} {Y S m : ℕ} :
    m ∈ dyadicLargeSquarePartExceptionalSet θ Y S ↔
      m ∈ dyadicSquarePartExceptionalSet θ Y ∧
        ∃ s w : ℕ, 0 < s ∧ S ≤ s ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w := by
  classical
  simp [dyadicLargeSquarePartExceptionalSet]

/-- The two local square-part families cover the dyadic exceptional set. -/
theorem dyadicSquarePartExceptionalSet_subset_small_union_large
    (θ : ℝ) (Y S : ℕ) :
    dyadicSquarePartExceptionalSet θ Y ⊆
      dyadicSmallSquarePartExceptionalSet θ Y S ∪
        dyadicLargeSquarePartExceptionalSet θ Y S := by
  intro m hm
  obtain ⟨s, w, hs, hw, _, _, hdecomp, hsf, _, _, _, _, _, _, _⟩ :=
    exists_dyadic_square_part_fundamental_data_of_mem hm
  by_cases hSs : S ≤ s
  · exact Finset.mem_union_right _ (mem_dyadicLargeSquarePartExceptionalSet.mpr
      ⟨hm, s, w, hs, hSs, hw, hdecomp, hsf⟩)
  · exact Finset.mem_union_left _ (mem_dyadicSmallSquarePartExceptionalSet.mpr
      ⟨hm, s, w, hs, lt_of_not_ge hSs, hw, hdecomp, hsf⟩)

/-- The local small and large square-part families are disjoint: their
positive square/squarefree decompositions must have the same root. -/
theorem disjoint_dyadicSmallSquarePartExceptionalSet_dyadicLargeSquarePartExceptionalSet
    (θ : ℝ) (Y S : ℕ) :
    Disjoint (dyadicSmallSquarePartExceptionalSet θ Y S)
      (dyadicLargeSquarePartExceptionalSet θ Y S) := by
  refine Finset.disjoint_left.mpr ?_
  intro m hsmall hlarge
  obtain ⟨_, s, w, hs, hslt, hw, hdecomp, hsf⟩ :=
    mem_dyadicSmallSquarePartExceptionalSet.mp hsmall
  obtain ⟨_, s', w', hs', hSle, hw', hdecomp', hsf'⟩ :=
    mem_dyadicLargeSquarePartExceptionalSet.mp hlarge
  obtain ⟨hss', _⟩ := square_part_decomposition_unique
    hs (lt_trans Nat.zero_lt_one hw) hs' (lt_trans Nat.zero_lt_one hw')
    hdecomp hdecomp' hsf hsf'
  subst s'
  exact (not_le_of_gt hslt) hSle

/-- The dyadic exceptional count splits exactly according to an arbitrary
square-part threshold. -/
theorem dyadicSquarePartExceptionalCount_eq_small_add_large
    (θ : ℝ) (Y S : ℕ) :
    dyadicSquarePartExceptionalCount θ Y =
      (dyadicSmallSquarePartExceptionalSet θ Y S).card +
        (dyadicLargeSquarePartExceptionalSet θ Y S).card := by
  unfold dyadicSquarePartExceptionalCount
  have hsubset := dyadicSquarePartExceptionalSet_subset_small_union_large θ Y S
  apply Nat.le_antisymm
  · calc
      (dyadicSquarePartExceptionalSet θ Y).card ≤
          (dyadicSmallSquarePartExceptionalSet θ Y S ∪
            dyadicLargeSquarePartExceptionalSet θ Y S).card :=
        Finset.card_le_card hsubset
      _ ≤ _ := Finset.card_union_le _ _
  · rw [← Finset.card_union_of_disjoint
      (disjoint_dyadicSmallSquarePartExceptionalSet_dyadicLargeSquarePartExceptionalSet
        θ Y S)]
    apply Finset.card_le_card
    intro m hm
    rcases Finset.mem_union.mp hm with hsmall | hlarge
    · exact (mem_dyadicSmallSquarePartExceptionalSet.mp hsmall).1
    · exact (mem_dyadicLargeSquarePartExceptionalSet.mp hlarge).1

/-- The small square-part contribution has the same finite transferred-family
reduction, with roots restricted to `[1, S)`. -/
theorem dyadicSmallSquarePartExceptionalSet_subset_transferred_union
    (θ : ℝ) (Y S : ℕ) :
    dyadicSmallSquarePartExceptionalSet θ Y S ⊆
      (Finset.Ico 1 S).biUnion fun s ↦
        (dyadicTransferredSquarefreeSet θ Y s).image fun w ↦ s ^ 2 * w := by
  classical
  intro m hm
  obtain ⟨hdyadic, s, w, hs, hsS, _, hdecomp, hsf⟩ :=
    mem_dyadicSmallSquarePartExceptionalSet.mp hm
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_Ico.mpr ⟨by omega, hsS⟩, ?_⟩
  exact Finset.mem_image.mpr
    ⟨w, mem_dyadicTransferredSquarefreeSet_of_mem_dyadicSquarePartExceptionalSet
      hdyadic hs hdecomp hsf, hdecomp.symm⟩

/-- The corresponding finite small-square-part counting reduction. -/
theorem dyadicSmallSquarePartExceptional_card_le_sum_transferred
    (θ : ℝ) (Y S : ℕ) :
    (dyadicSmallSquarePartExceptionalSet θ Y S).card ≤
      ∑ s ∈ Finset.Ico 1 S, (dyadicTransferredSquarefreeSet θ Y s).card := by
  classical
  calc
    (dyadicSmallSquarePartExceptionalSet θ Y S).card ≤
        ((Finset.Ico 1 S).biUnion fun s ↦
          (dyadicTransferredSquarefreeSet θ Y s).image fun w ↦ s ^ 2 * w).card :=
      Finset.card_le_card
        (dyadicSmallSquarePartExceptionalSet_subset_transferred_union θ Y S)
    _ ≤ ∑ s ∈ Finset.Ico 1 S,
        ((dyadicTransferredSquarefreeSet θ Y s).image fun w ↦ s ^ 2 * w).card :=
      Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le

end PellPaper
