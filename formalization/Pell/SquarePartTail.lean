import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Pell.SquareParts

/-!
# A finite bound for the large-square-divisor tail

This file formalizes the counting step underlying the large-square-part tail
in the subsection "Square parts" of `main.tex`.  Among positive natural numbers
at most `X`, those divisible by `s ^ 2` for some `s ≥ S` form a finite union of
sets of multiples.  Its cardinality is at most

`∑ s ∈ Finset.Icc S X, X / s ^ 2`.

Here division is natural-number division, so every summand is the exact count
of positive multiples.  No squarefreeness or Pell condition is needed for this
upper bound.  The later analytic estimate for this sum is not asserted here.
-/

open scoped BigOperators

namespace PellPaper

/-- The positive multiples of `d` at most `X`. -/
def positiveMultiplesUpTo (X d : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter fun m => d ∣ m

@[simp]
theorem mem_positiveMultiplesUpTo {X d m : ℕ} :
    m ∈ positiveMultiplesUpTo X d ↔ 0 < m ∧ m ≤ X ∧ d ∣ m := by
  simp [positiveMultiplesUpTo, and_assoc]

/-- The count also holds for `d = 0`, when both sides are zero. -/
@[simp]
theorem card_positiveMultiplesUpTo (X d : ℕ) :
    (positiveMultiplesUpTo X d).card = X / d := by
  exact Nat.Ioc_filter_dvd_card_eq_div X d

/-- Positive integers at most `X` carrying a square divisor with root at least
`S`.  The existential quantifier is unrestricted; finiteness comes from the
ambient interval. -/
noncomputable def squareDivisorTail (X S : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 X).filter fun m => ∃ s : ℕ, S ≤ s ∧ s ^ 2 ∣ m

@[simp]
theorem mem_squareDivisorTail {X S m : ℕ} :
    m ∈ squareDivisorTail X S ↔
      0 < m ∧ m ≤ X ∧ ∃ s : ℕ, S ≤ s ∧ s ^ 2 ∣ m := by
  classical
  simp [squareDivisorTail, and_assoc]

/-- A square divisor of a positive integer has root at most that integer,
and therefore at most its cutoff.  This bounds the existential witness in
`squareDivisorTail` by a finite interval. -/
theorem square_divisor_le_cutoff {X m s : ℕ} (hm : 0 < m) (hmX : m ≤ X)
    (hs : s ^ 2 ∣ m) : s ≤ X := by
  exact (Nat.le_of_dvd hm ((dvd_pow_self s (by decide : 2 ≠ 0)).trans hs)).trans hmX

/-- An exact finite-union description of the tail. -/
theorem squareDivisorTail_eq_biUnion (X S : ℕ) :
    squareDivisorTail X S =
      (Finset.Icc S X).biUnion (fun s => positiveMultiplesUpTo X (s ^ 2)) := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨hm0, hmX, s, hSs, hsm⟩ := mem_squareDivisorTail.mp hm
    exact Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_Icc.mpr ⟨hSs, square_divisor_le_cutoff hm0 hmX hsm⟩,
        mem_positiveMultiplesUpTo.mpr ⟨hm0, hmX, hsm⟩⟩
  · intro hm
    obtain ⟨s, hs, hsm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hm0, hmX, hdvd⟩ := mem_positiveMultiplesUpTo.mp hsm
    exact mem_squareDivisorTail.mpr
      ⟨hm0, hmX, s, (Finset.mem_Icc.mp hs).1, hdvd⟩

/-- The finite union bound for large square divisors.  No positivity assumption
on the threshold or cutoff is needed. -/
theorem squareDivisorTail_card_le (X S : ℕ) :
    (squareDivisorTail X S).card ≤ ∑ s ∈ Finset.Icc S X, X / s ^ 2 := by
  rw [squareDivisorTail_eq_biUnion]
  calc
    _ ≤ ∑ s ∈ Finset.Icc S X, (positiveMultiplesUpTo X (s ^ 2)).card :=
      Finset.card_biUnion_le
    _ = _ := by simp

/-- Increasing the cutoff and decreasing the threshold enlarge the tail. -/
theorem squareDivisorTail_mono {X Y S T : ℕ} (hXY : X ≤ Y) (hTS : T ≤ S) :
    squareDivisorTail X S ⊆ squareDivisorTail Y T := by
  intro m hm
  obtain ⟨hm0, hmX, s, hSs, hsm⟩ := mem_squareDivisorTail.mp hm
  exact mem_squareDivisorTail.mpr ⟨hm0, hmX.trans hXY, s, hTS.trans hSs, hsm⟩

/-- A threshold beyond the cutoff leaves no positive integer in the tail. -/
theorem squareDivisorTail_eq_empty_of_lt {X S : ℕ} (hXS : X < S) :
    squareDivisorTail X S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  obtain ⟨hm0, hmX, s, hSs, hsm⟩ := mem_squareDivisorTail.mp hm
  exact (not_le_of_gt hXS) (hSs.trans (square_divisor_le_cutoff hm0 hmX hsm))

/-- A square-part decomposition immediately places its radicand in the tail.
The squarefree condition on `w` is unnecessary for this direction. -/
theorem mem_squareDivisorTail_of_decomposition {X S m s w : ℕ}
    (hm : 0 < m) (hmX : m ≤ X) (hSs : S ≤ s) (hdecomp : m = s ^ 2 * w) :
    m ∈ squareDivisorTail X S := by
  exact mem_squareDivisorTail.mpr ⟨hm, hmX, s, hSs, ⟨w, hdecomp⟩⟩

/-- Any finite family of positive radicands satisfying the tail condition
inherits the sum-of-floors bound. -/
theorem card_le_square_divisor_sum {A : Finset ℕ} {X S : ℕ}
    (hA : ∀ m ∈ A, 0 < m ∧ m ≤ X ∧ ∃ s : ℕ, S ≤ s ∧ s ^ 2 ∣ m) :
    A.card ≤ ∑ s ∈ Finset.Icc S X, X / s ^ 2 := by
  apply le_trans (Finset.card_le_card (show A ⊆ squareDivisorTail X S from ?_))
    (squareDivisorTail_card_le X S)
  intro m hm
  exact mem_squareDivisorTail.mpr (hA m hm)

/-- A directly applicable version for a family supplied with square-part
decompositions.  Additional conditions such as squarefreeness or a small Pell
solution may be retained in the definition of `A`. -/
theorem card_le_square_divisor_sum_of_decompositions {A : Finset ℕ} {X S : ℕ}
    (hA : ∀ m ∈ A, 0 < m ∧ m ≤ X ∧
      ∃ s w : ℕ, S ≤ s ∧ m = s ^ 2 * w) :
    A.card ≤ ∑ s ∈ Finset.Icc S X, X / s ^ 2 := by
  apply card_le_square_divisor_sum
  intro m hm
  obtain ⟨hm0, hmX, s, w, hSs, hdecomp⟩ := hA m hm
  exact ⟨hm0, hmX, s, hSs, ⟨w, hdecomp⟩⟩

end PellPaper
