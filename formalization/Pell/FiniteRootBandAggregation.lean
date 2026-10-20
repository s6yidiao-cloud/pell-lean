import Pell.FiniteRootBandBound

/-!
# Aggregating a finite cover of square-part root bands

The fixed-height argument supplies a bound on one closed root band at a
time.  This module packages a finite family of such bands and proves the
purely combinatorial aggregation step.  A cover may overlap: nonnegativity
of the fiber cardinalities permits summing all bands without choosing a
disjoint refinement.

The final conditional theorem chooses one fixed-height constant for each
member of a prescribed finite family.  It deliberately leaves the resulting
finite sum of scaled power bounds unevaluated.  In particular, this module
does not choose the bands or their heights, and does not assert a Pell power
saving.
-/

open scoped BigOperators

namespace PellPaper

/-- A finite family of closed natural root bands which covers every root in
the small range `[1, S)`.  The bands are allowed to overlap and may include
roots outside that range; later analytic parameter selection supplies the
positive lower-endpoint and individual-cost hypotheses where needed. -/
structure FiniteRootBandCover (S : ℕ) where
  bandCount : ℕ
  lower : Fin bandCount → ℕ
  upper : Fin bandCount → ℕ
  covers : Finset.Ico 1 S ⊆
    Finset.univ.biUnion fun i => Finset.Icc (lower i) (upper i)

namespace FiniteRootBandCover

/-- The closed natural interval attached to one band of a finite cover. -/
def band {S : ℕ} (cover : FiniteRootBandCover S) (i : Fin cover.bandCount) : Finset ℕ :=
  Finset.Icc (cover.lower i) (cover.upper i)

/-- The union of all bands in the cover. -/
def bandUnion {S : ℕ} (cover : FiniteRootBandCover S) : Finset ℕ :=
  Finset.univ.biUnion cover.band

/-- The packaged cover condition, rewritten using `band` and `bandUnion`. -/
theorem smallRootRange_subset_bandUnion {S : ℕ} (cover : FiniteRootBandCover S) :
    Finset.Ico 1 S ⊆ cover.bandUnion := by
  change Finset.Ico 1 S ⊆
    Finset.univ.biUnion fun i => Finset.Icc (cover.lower i) (cover.upper i)
  exact cover.covers

end FiniteRootBandCover

/-- The sum over a finite union is at most the sum of the individual sums
when every term is nonnegative.  This is the only place where overlap of the
root bands is charged; it introduces no hidden disjointness assumption. -/
theorem sum_biUnion_le_sum_of_nonneg
    {ι α : Type*} [DecidableEq α] (I : Finset ι) (bands : ι → Finset α)
    (f : α → ℝ) (hnonneg : ∀ x, 0 ≤ f x) :
    (∑ x ∈ I.biUnion bands, f x) ≤
      ∑ i ∈ I, ∑ x ∈ bands i, f x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi hI =>
      rw [Finset.biUnion_insert]
      have hinter :
          0 ≤ ∑ x ∈ bands i ∩ I.biUnion bands, f x :=
        Finset.sum_nonneg fun x _ => hnonneg x
      have hunion := Finset.sum_union_inter (s₁ := bands i)
        (s₂ := I.biUnion bands) (f := f)
      calc
        (∑ x ∈ bands i ∪ I.biUnion bands, f x) ≤
            (∑ x ∈ bands i, f x) + (∑ x ∈ I.biUnion bands, f x) := by
              linarith
        _ ≤ (∑ x ∈ bands i, f x) +
            (∑ j ∈ I, ∑ x ∈ bands j, f x) := by
              gcongr
        _ = ∑ j ∈ insert i I, ∑ x ∈ bands j, f x := by
              rw [Finset.sum_insert hi]

/-- A finite root-band cover aggregates any supplied real bound for the
fiber sum on each band.  Overlapping bands are harmless because the
transferred-fiber cardinalities are nonnegative. -/
theorem sum_dyadicTransferredSquarefreeSet_card_le_sum_of_finiteRootBandCover
    {theta : ℝ} {Y S : ℕ} (cover : FiniteRootBandCover S)
    (B : Fin cover.bandCount → ℝ)
    (hband : ∀ i : Fin cover.bandCount,
      (∑ s ∈ cover.band i,
        ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤ B i) :
    (∑ s ∈ Finset.Ico 1 S,
      ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤
        ∑ i : Fin cover.bandCount, B i := by
  let f : ℕ → ℝ := fun s =>
    ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)
  have hnonneg : ∀ s, 0 ≤ f s := fun s => Nat.cast_nonneg _
  calc
    (∑ s ∈ Finset.Ico 1 S,
        ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤
        ∑ s ∈ cover.bandUnion, f s := by
          simpa [f] using
            (Finset.sum_le_sum_of_subset_of_nonneg
              cover.smallRootRange_subset_bandUnion
              (fun s _ _ => hnonneg s))
    _ ≤ ∑ i ∈ Finset.univ, ∑ s ∈ cover.band i, f s := by
          exact sum_biUnion_le_sum_of_nonneg Finset.univ cover.band f hnonneg
    _ ≤ ∑ i : Fin cover.bandCount, B i := by
          simpa [f] using Finset.sum_le_sum fun i _ => hband i

/-- The small-square-part exceptional set is bounded by a finite root-band
cover whenever the corresponding transferred-fiber band sums are bounded. -/
theorem dyadicSmallSquarePartExceptionalSet_card_le_sum_of_finiteRootBandCover
    {theta : ℝ} {Y S : ℕ} (cover : FiniteRootBandCover S)
    (B : Fin cover.bandCount → ℝ)
    (hband : ∀ i : Fin cover.bandCount,
      (∑ s ∈ cover.band i,
        ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤ B i) :
    ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
      ∑ i : Fin cover.bandCount, B i := by
  calc
    ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
        ∑ s ∈ Finset.Ico 1 S,
          ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ) := by
            exact_mod_cast
              dyadicSmallSquarePartExceptional_card_le_sum_transferred theta Y S
    _ ≤ ∑ i : Fin cover.bandCount, B i :=
      sum_dyadicTransferredSquarefreeSet_card_le_sum_of_finiteRootBandCover
        cover B hband

/-- Applying the fixed-height finite-band theorem once to every band of a
prescribed finite cover gives a finite, explicit sum of scaled fiber costs.
It inherits the one-band uniformity supplied by `FiniteRootBandBound`, but
makes no cross-cover uniformity or power-saving claim. -/
theorem exists_dyadicSmallSquarePartExceptionalSet_card_le_finiteRootBandPowerSum_of_FixedHeightSquarefree
    (hfixed : FixedHeightSquarefree) {theta : ℝ} {Y S : ℕ}
    (cover : FiniteRootBandCover S)
    (phi d : Fin cover.bandCount → ℝ)
    (hphi : ∀ i, 3 ≤ phi i) (hdpos : ∀ i, 0 < d i)
    (hd : ∀ i, d i < Delta (phi i)) (htheta : ∀ i, theta ≤ phi i)
    (hlower : ∀ i, 0 < cover.lower i)
    (hinterval : ∀ i, cover.lower i ≤ cover.upper i)
    (hbudget : ∀ i,
      (cover.upper i : ℝ) ^ (2 * phi i) ≤
        (Y : ℝ) ^ (phi i - theta)) :
    ∃ C : Fin cover.bandCount → ℝ, (∀ i, 0 ≤ C i) ∧
      ((dyadicSmallSquarePartExceptionalSet theta Y S).card : ℝ) ≤
        ∑ i : Fin cover.bandCount,
          ((cover.upper i - cover.lower i + 1 : ℕ) : ℝ) * C i *
            (((2 * Y - 1) / (cover.lower i) ^ 2 : ℕ) : ℝ) ^ (1 - d i) := by
  have hband : ∀ i : Fin cover.bandCount, ∃ C : ℝ, 0 ≤ C ∧
      (∑ s ∈ cover.band i,
        ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤
          ((cover.upper i - cover.lower i + 1 : ℕ) : ℝ) * C *
            (((2 * Y - 1) / (cover.lower i) ^ 2 : ℕ) : ℝ) ^ (1 - d i) := by
    intro i
    obtain ⟨C, hC, hCbound⟩ :=
      exists_sum_dyadicTransferredSquarefreeSet_card_rootBand_scaled_power_bound_of_FixedHeightSquarefree
        hfixed (hphi i) (hdpos i) (hd i)
    refine ⟨C, hC, ?_⟩
    simpa [FiniteRootBandCover.band] using
      hCbound theta (htheta i) Y (cover.lower i) (cover.upper i)
        (hlower i) (hinterval i) (hbudget i)
  choose C hC hCbound using hband
  refine ⟨C, hC, ?_⟩
  exact dyadicSmallSquarePartExceptionalSet_card_le_sum_of_finiteRootBandCover
    cover _ hCbound

end PellPaper
