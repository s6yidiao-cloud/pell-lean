import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Int.Interval

/-!
# Counting separated real centers in an interval

This finite packing lemma counts a genuinely separated family of real
centers in a bounded interval.  The constant is explicit and no lattice,
curve, or counting premise is supplied.  It is the one-dimensional input
for the non-axis short-vector count in normalized slope lattices.
-/

namespace PellPaper

noncomputable section

/-- A `sep`-separated finite family in `[L,R]` contains at most
`1 + (R-L)/sep` points.  Separation is imposed on distinct indices, so the
statement also excludes repeated centers. -/
theorem card_le_one_add_div_of_separated_real_centers
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (L R sep : ℝ)
    (hsep : 0 < sep) (hLR : L ≤ R)
    (hbounds : ∀ i ∈ J, L ≤ z i ∧ z i ≤ R)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|) :
    (J.card : ℝ) ≤ 1 + (R - L) / sep := by
  classical
  let f : ι → ℕ := fun i => ⌊(z i - L) / sep⌋₊
  let N : ℕ := ⌊(R - L) / sep⌋₊
  have hmaps : Set.MapsTo f (↑J : Set ι) (↑(Finset.range (N + 1)) : Set ℕ) := by
    intro i hi
    apply Finset.mem_range.mpr
    have hle : f i ≤ N := Nat.floor_mono
      (div_le_div_of_nonneg_right (sub_le_sub_right (hbounds i hi).2 L) hsep.le)
    omega
  have hinj : Set.InjOn f (↑J : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    have hi0 : 0 ≤ (z i - L) / sep :=
      div_nonneg (sub_nonneg.mpr (hbounds i hi).1) hsep.le
    have hj0 : 0 ≤ (z j - L) / sep :=
      div_nonneg (sub_nonneg.mpr (hbounds j hj).1) hsep.le
    have hilow := Nat.floor_le hi0
    have hjlow := Nat.floor_le hj0
    have hiup := Nat.lt_floor_add_one ((z i - L) / sep)
    have hjup := Nat.lt_floor_add_one ((z j - L) / sep)
    have heq : (⌊(z i - L) / sep⌋₊ : ℝ) = ⌊(z j - L) / sep⌋₊ := by
      exact_mod_cast hij
    have hsmall : |(z i - L) / sep - (z j - L) / sep| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hlarge : 1 ≤ |(z i - L) / sep - (z j - L) / sep| := by
      rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hsep]
      exact (le_div_iff₀ hsep).mpr (by simpa using hseparated i hi j hj hne)
    linarith
  have hcard : J.card ≤ N + 1 := by
    simpa using Finset.card_le_card_of_injOn f hmaps hinj
  have hfloor : (N : ℝ) ≤ (R - L) / sep :=
    Nat.floor_le (div_nonneg (sub_nonneg.mpr hLR) hsep.le)
  have hcast : (J.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hcard
  linarith

end

end PellPaper
