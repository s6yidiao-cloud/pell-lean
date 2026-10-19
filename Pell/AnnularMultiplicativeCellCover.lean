import Pell.DyadicLocalRatioCover

/-!
# A finite annular multiplicative cover on the real line

This module gives a literal finite cover for nonzero real numbers whose
absolute values lie in the annulus `F⁻² ≤ |x| ≤ F²`.  The indices consist of
one of the two signs, a binary scale, and one of `2M` multiplicative mesh
positions.  Thus the exact number of indices is

`4 * M * dyadicScaleCount (⌈F⌉₊ ^ 4)`.

The result is deliberately only a geometric covering interface.  It makes no
claim about compatibility with a second ratio, determinants, or point counts.
-/

namespace PellPaper

noncomputable section

/-- The lower radius `F⁻²` of the annulus, written without negative powers. -/
def annularLowerRadius (F : ℝ) : ℝ := (F ^ 2)⁻¹

/-- A natural height which dominates the normalized annular range `F⁴` when
`F ≥ 1`. -/
def annularDyadicHeight (F : ℝ) : ℕ := ⌈F⌉₊ ^ 4

/-- The exact number of binary scales used by the annular cover. -/
def annularDyadicScaleCount (F : ℝ) : ℕ :=
  dyadicScaleCount (annularDyadicHeight F)

/-- The two literal signs used by the cover. -/
def annularSigns : Finset ℤ := {-1, 1}

/-- An annular cell index: sign, binary scale, and multiplicative mesh index. -/
abbrev AnnularMultiplicativeCellIndex := ℤ × (ℕ × ℕ)

/-- The finite index family for the annular multiplicative cover. -/
def annularMultiplicativeCellIndices (F : ℝ) (M : ℕ) :
    Finset AnnularMultiplicativeCellIndex :=
  annularSigns.product
    ((Finset.range (annularDyadicScaleCount F)).product
      (Finset.range (2 * M)))

/-- The left endpoint of the `j`th binary magnitude range. -/
def annularDyadicStart (F : ℝ) (j : ℕ) : ℝ :=
  annularLowerRadius F * ((2 ^ j : ℕ) : ℝ)

/-- The centre (left endpoint) of the `k`th relative mesh window inside the
`j`th binary magnitude range. -/
def annularMultiplicativeCenter (F : ℝ) (M j k : ℕ) : ℝ :=
  annularDyadicStart F j * localRatioMeshStep M ^ k

/-- The pointwise predicate defining a signed annular multiplicative cell. -/
def InAnnularMultiplicativeCell
    (F : ℝ) (M : ℕ) (i : AnnularMultiplicativeCellIndex) (x : ℝ) : Prop :=
  x = (i.1 : ℝ) * |x| ∧
    annularMultiplicativeCenter F M i.2.1 i.2.2 ≤ |x| ∧
      |x| ≤ annularMultiplicativeCenter F M i.2.1 i.2.2 *
        localRatioMeshStep M

/-- The literal portion of a finite real set lying in one annular
multiplicative cell. -/
noncomputable def annularMultiplicativeCell
    (S : Finset ℝ) (F : ℝ) (M : ℕ) (i : AnnularMultiplicativeCellIndex) :
    Finset ℝ := by
  classical
  exact S.filter (InAnnularMultiplicativeCell F M i)

theorem annularLowerRadius_pos {F : ℝ} (hF : 1 ≤ F) :
    0 < annularLowerRadius F := by
  unfold annularLowerRadius
  positivity

theorem annularDyadicStart_pos {F : ℝ} (hF : 1 ≤ F) (j : ℕ) :
    0 < annularDyadicStart F j := by
  unfold annularDyadicStart
  exact mul_pos (annularLowerRadius_pos hF) (by positivity)

@[simp] theorem card_annularSigns : annularSigns.card = 2 := by
  norm_num [annularSigns]

/-- Membership in the finite index family is exactly the literal sign and
the two displayed range conditions. -/
theorem mem_annularMultiplicativeCellIndices
    {F : ℝ} {M : ℕ} {i : AnnularMultiplicativeCellIndex} :
    i ∈ annularMultiplicativeCellIndices F M ↔
      i.1 ∈ annularSigns ∧
        i.2.1 < annularDyadicScaleCount F ∧ i.2.2 < 2 * M := by
  simp [annularMultiplicativeCellIndices]

/-- The exact index count: two signs, the displayed dyadic scale count, and
`2M` relative mesh positions. -/
@[simp] theorem card_annularMultiplicativeCellIndices (F : ℝ) (M : ℕ) :
    (annularMultiplicativeCellIndices F M).card =
      4 * M * annularDyadicScaleCount F := by
  simp [annularMultiplicativeCellIndices]
  ring

/-- Every magnitude in the annulus lies between one selected binary start
and four times that start.  The chosen scale is the binary logarithm of the
floor of the normalized magnitude `|x| / F⁻²`. -/
theorem exists_annularDyadicIntervalIndex
    {F x : ℝ} (hF : 1 ≤ F)
    (hlower : annularLowerRadius F ≤ |x|)
    (hupper : |x| ≤ F ^ 2) :
    ∃ j ∈ Finset.range (annularDyadicScaleCount F),
      annularDyadicStart F j ≤ |x| ∧
        |x| ≤ 4 * annularDyadicStart F j := by
  let b : ℝ := annularLowerRadius F
  let y : ℝ := |x| / b
  let m : ℕ := ⌊y⌋₊
  have hb : 0 < b := by
    simpa only [b] using annularLowerRadius_pos hF
  have hyone : 1 ≤ y := by
    dsimp only [y]
    exact (le_div_iff₀ hb).2 (by simpa only [b, one_mul] using hlower)
  have hyzero : 0 ≤ y := le_trans (by norm_num) hyone
  have hFpos : 0 < F := lt_of_lt_of_le (by norm_num) hF
  have hbinv : b = (F ^ 2)⁻¹ := rfl
  have hyupper : y ≤ F ^ 4 := by
    apply (div_le_iff₀ hb).2
    rw [hbinv]
    field_simp [hFpos.ne']
    nlinarith
  have hFceil : F ≤ (⌈F⌉₊ : ℝ) := Nat.le_ceil F
  have hceilnonneg : 0 ≤ (⌈F⌉₊ : ℝ) := by positivity
  have hheight : F ^ 4 ≤ ((annularDyadicHeight F : ℕ) : ℝ) := by
    simpa only [annularDyadicHeight, Nat.cast_pow] using
      (pow_le_pow_left₀ hFpos.le hFceil 4)
  have hmcast : (m : ℝ) ≤ ((annularDyadicHeight F : ℕ) : ℝ) := by
    calc
      (m : ℝ) ≤ y := by
        dsimp only [m]
        exact Nat.floor_le hyzero
      _ ≤ F ^ 4 := hyupper
      _ ≤ ((annularDyadicHeight F : ℕ) : ℝ) := hheight
  have hmheight : m ≤ annularDyadicHeight F := by exact_mod_cast hmcast
  have hmone : 1 ≤ m := by
    dsimp only [m]
    exact Nat.le_floor (by simpa only [Nat.cast_one] using hyone)
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmone
  let j : ℕ := Nat.log 2 m
  have hjmem : j ∈ Finset.range (annularDyadicScaleCount F) := by
    dsimp only [j, annularDyadicScaleCount]
    exact log_mem_dyadicScaleRange hmpos hmheight
  have hjlowerNat : 2 ^ j ≤ m := by
    dsimp only [j]
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hmpos)
  have hjupperNat : m + 1 ≤ 2 ^ (j + 1) := by
    dsimp only [j]
    exact Nat.succ_le_iff.mpr
      (by simpa [Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self Nat.one_lt_two m)
  have hmle : (m : ℝ) ≤ y := by
    dsimp only [m]
    exact Nat.floor_le hyzero
  have hylt : y < (m : ℝ) + 1 := by
    dsimp only [m]
    exact Nat.lt_floor_add_one y
  have hpowle : (((2 ^ j : ℕ) : ℝ)) ≤ y := by
    exact (by exact_mod_cast hjlowerNat : (((2 ^ j : ℕ) : ℝ)) ≤ (m : ℝ)).trans hmle
  have hyltpow : y < (((2 ^ (j + 1) : ℕ) : ℝ)) := by
    exact hylt.trans_le (by exact_mod_cast hjupperNat)
  have hby : b * y = |x| := by
    dsimp only [y]
    field_simp [hb.ne']
  refine ⟨j, hjmem, ?_, ?_⟩
  · rw [annularDyadicStart, ← hby]
    exact mul_le_mul_of_nonneg_left hpowle hb.le
  · have habslt : |x| < b * (((2 ^ (j + 1) : ℕ) : ℝ)) := by
      rw [← hby]
      exact mul_lt_mul_of_pos_left hyltpow hb
    calc
      |x| ≤ b * (((2 ^ (j + 1) : ℕ) : ℝ)) := habslt.le
      _ = 2 * annularDyadicStart F j := by
        simp only [annularDyadicStart, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ 4 * annularDyadicStart F j := by
        have hs := (annularDyadicStart_pos hF j).le
        linarith

/-- A nonzero real number has one of the two literal signed-magnitude
representations used by the cover. -/
theorem exists_annularSign {x : ℝ} (hx : x ≠ 0) :
    ∃ ε ∈ annularSigns, x = (ε : ℝ) * |x| := by
  by_cases hxpos : 0 < x
  · refine ⟨1, by norm_num [annularSigns], ?_⟩
    simp [abs_of_pos hxpos]
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    refine ⟨-1, by norm_num [annularSigns], ?_⟩
    simp [abs_of_neg hxneg]

/-- Pointwise cover: every nonzero point of the annulus belongs to a literal
finite signed/dyadic/multiplicative cell. -/
theorem exists_mem_annularMultiplicativeCell
    {F x : ℝ} {M : ℕ} (hF : 1 ≤ F) (hM : 0 < M) (hx : x ≠ 0)
    (hlower : annularLowerRadius F ≤ |x|)
    (hupper : |x| ≤ F ^ 2) :
    ∃ i ∈ annularMultiplicativeCellIndices F M,
      InAnnularMultiplicativeCell F M i x := by
  obtain ⟨j, hjmem, hjlower, hjupper⟩ :=
    exists_annularDyadicIntervalIndex hF hlower hupper
  obtain ⟨k, hk, hklower, hkupper⟩ :=
    exists_localRatioMeshInterval_index_of_between hM
      (annularDyadicStart_pos hF j) hjlower hjupper
  obtain ⟨ε, hε, hsign⟩ := exists_annularSign hx
  refine ⟨(ε, (j, k)), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨hε, Finset.mem_product.mpr
        ⟨hjmem, Finset.mem_range.mpr hk⟩⟩
  · exact ⟨hsign, by simpa [annularMultiplicativeCenter] using hklower,
      by simpa [annularMultiplicativeCenter] using hkupper⟩

/-- Membership in a literal finite-set cell retains the ambient-set evidence
and exposes the exact signed relative window. -/
theorem mem_annularMultiplicativeCell
    {S : Finset ℝ} {F : ℝ} {M : ℕ} {i : AnnularMultiplicativeCellIndex}
    {x : ℝ} (hx : x ∈ annularMultiplicativeCell S F M i) :
    x ∈ S ∧ InAnnularMultiplicativeCell F M i x := by
  classical
  simpa only [annularMultiplicativeCell] using (Finset.mem_filter.mp hx)

/-- Each literal annular cell is a subfinset of its ambient finite set. -/
theorem annularMultiplicativeCell_subset
    (S : Finset ℝ) (F : ℝ) (M : ℕ) (i : AnnularMultiplicativeCellIndex) :
    annularMultiplicativeCell S F M i ⊆ S := by
  intro x hx
  exact (mem_annularMultiplicativeCell hx).1

/-- The exact common signed-magnitude and relative-width data supplied by a
cell membership proof. -/
theorem annularMultiplicativeCell_commonWindow
    {S : Finset ℝ} {F : ℝ} {M : ℕ} {i : AnnularMultiplicativeCellIndex}
    {x : ℝ} (hx : x ∈ annularMultiplicativeCell S F M i) :
    x = (i.1 : ℝ) * |x| ∧
      annularMultiplicativeCenter F M i.2.1 i.2.2 ≤ |x| ∧
        |x| ≤ annularMultiplicativeCenter F M i.2.1 i.2.2 *
          (1 + 1 / (M : ℝ)) := by
  simpa [InAnnularMultiplicativeCell, localRatioMeshStep] using
    (mem_annularMultiplicativeCell hx).2

/-- A finite family of nonzero annular points is covered by the literal
finite family of annular multiplicative cells. -/
theorem annularFinset_subset_biUnion_cells
    (S : Finset ℝ) {F : ℝ} {M : ℕ} (hF : 1 ≤ F) (hM : 0 < M)
    (hS : ∀ x ∈ S,
      x ≠ 0 ∧ annularLowerRadius F ≤ |x| ∧ |x| ≤ F ^ 2) :
    S ⊆ (annularMultiplicativeCellIndices F M).biUnion
      (annularMultiplicativeCell S F M) := by
  intro x hx
  obtain ⟨hxne, hxlower, hxupper⟩ := hS x hx
  obtain ⟨i, hi, hcell⟩ :=
    exists_mem_annularMultiplicativeCell hF hM hxne hxlower hxupper
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, ?_⟩
  classical
  simpa only [annularMultiplicativeCell] using
    (Finset.mem_filter.mpr ⟨hx, hcell⟩)

/-- Overlap-safe cardinality consequence of the literal finite cover. -/
theorem card_annularFinset_le_sum_card_cells
    (S : Finset ℝ) {F : ℝ} {M : ℕ} (hF : 1 ≤ F) (hM : 0 < M)
    (hS : ∀ x ∈ S,
      x ≠ 0 ∧ annularLowerRadius F ≤ |x| ∧ |x| ≤ F ^ 2) :
    S.card ≤ ∑ i ∈ annularMultiplicativeCellIndices F M,
      (annularMultiplicativeCell S F M i).card := by
  exact (Finset.card_le_card
    (annularFinset_subset_biUnion_cells S hF hM hS)).trans
      Finset.card_biUnion_le

end

end PellPaper
