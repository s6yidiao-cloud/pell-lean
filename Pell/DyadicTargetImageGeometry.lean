import Pell.DyadicSourceTargetCellPairs
import Pell.DyadicRawPairPrimitivity

/-!
# Literal finite target images of actual source/target cells

These definitions keep the original dyadic tuples and right-ceiling target
index. The image forgets the source coordinates, so its cardinality is not
claimed equal to the number of tuples. Actual arithmetic supplies primitive
target vectors, the radius-two slope bound, and a nonempty minimum witness.
-/

namespace PellPaper

noncomputable section

/-- The literal source-ratio cell further filtered by its target ceiling. -/
def dyadicSourceTargetTupleCell (theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) (M j : ℕ) (k : ℤ) : Finset (ℕ × ℕ × ℕ × ℕ) := by
  classical
  exact (dyadicFactorBoxLocalRatioCell theta Y i M j).filter
    (fun q => dyadicFactorBoxTargetRightIndex i M q = k)

/-- Its literal finite image in target-coordinate order `(v,u)`. -/
def dyadicSourceTargetImage (theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) (M j : ℕ) (k : ℤ) : Finset (Fin 2 → ℤ) := by
  classical
  exact (dyadicSourceTargetTupleCell theta Y i M j k).image
    (fun q => ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)])

/-- Image membership retains an actual original tuple, without a claim of
unique source recovery. -/
theorem mem_dyadicSourceTargetImage_iff
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M j : ℕ) (k : ℤ)
    (y : Fin 2 → ℤ) :
    y ∈ dyadicSourceTargetImage theta Y i M j k ↔
      ∃ q ∈ dyadicFactorBoxLocalRatioCell theta Y i M j,
        dyadicFactorBoxTargetRightIndex i M q = k ∧
          ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] = y := by
  classical
  simp only [dyadicSourceTargetImage, Finset.mem_image,
    dyadicSourceTargetTupleCell, Finset.mem_filter]
  constructor
  · rintro ⟨q, ⟨hq, hk⟩, hy⟩
    exact ⟨q, hq, hk, hy⟩
  · rintro ⟨q, hq, hk, hy⟩
    exact ⟨q, ⟨hq, hk⟩, hy⟩

/-- Every actual image vector is primitive and lies in the literal
radius-two slope ball at the shared right-ceiling index. No positivity of
the localization parameter is needed for these two facts. -/
theorem dyadicSourceTargetImage_primitive_and_supNorm
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {M j : ℕ} {k : ℤ}
    {y : Fin 2 → ℤ} (hy : y ∈ dyadicSourceTargetImage theta Y i M j k) :
    IsCoprime (y 0) (y 1) ∧
      slopeVectorSupNorm ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ)
        (M : ℝ) (k : ℝ) (y 0, y 1) ≤ 2 := by
  obtain ⟨q, hq, hk, rfl⟩ :=
    (mem_dyadicSourceTargetImage_iff theta Y i M j k y).mp hy
  have hambient := (mem_dyadicFactorBoxLocalRatioCell hq).1
  obtain ⟨hfactor, hbox⟩ := Finset.mem_inter.mp hambient
  have hc := mem_dyadicFactorTuples.mp hfactor
  have hnorm := dyadicFactorBoxTargetRightIndex_supNorm_le_two M hbox
  rw [hk] at hnorm
  exact ⟨(dyadicFactorCondition_primitive_raw_pairs hc).2, hnorm⟩

/-- A nonempty actual target image gives a nonzero vector witnessing that
the actual first minimum is at most two. Empty cells give no such bound. -/
theorem firstSlopeSupNorm_le_two_of_dyadicSourceTargetImage_nonempty
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {M j : ℕ} {k : ℤ}
    (hM : 0 < M) (hT : (dyadicSourceTargetImage theta Y i M j k).Nonempty) :
    firstSlopeSupNorm ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ)
      (M : ℝ) (k : ℝ) ≤ 2 := by
  obtain ⟨y, hy⟩ := hT
  obtain ⟨hprim, hnorm⟩ := dyadicSourceTargetImage_primitive_and_supNorm hy
  have hn : (y 0, y 1) ≠ (0 : ℤ × ℤ) := by
    intro hz
    have h0 : y 0 = 0 := congrArg Prod.fst hz
    have h1 : y 1 = 0 := congrArg Prod.snd hz
    obtain ⟨a, b, hab⟩ := hprim
    simp [h0, h1] at hab
  exact (firstSlopeSupNorm_le _ _ _ _ (by positivity) (by positivity)
    (by exact_mod_cast hM) (y 0, y 1) hn).trans hnorm

end

end PellPaper
