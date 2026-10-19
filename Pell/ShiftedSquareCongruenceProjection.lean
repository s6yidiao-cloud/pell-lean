import Pell.ShiftedSquareBlock
import Mathlib.Tactic

/-!
# Exact projection of shifted-square blocks to congruence pairs

For a point `d^2 w = n^2 + a`, the pair `(d,n)` satisfies the congruence
`d^2 ∣ n^2 + a`.  Conversely, `w` is uniquely determined once the positive
denominator `d` and numerator `n` are fixed.  This file records that exact
finite injection.  It deliberately makes no analytic estimate for the number
of congruence pairs.
-/

namespace PellPaper

noncomputable section

/-- The exact half-open family of positive pairs `(d,n)` satisfying the
shifted-square congruence `d^2 ∣ n^2 + a`. -/
noncomputable def shiftedSquareCongruencePairs
    (a : ℤ) (D N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Ico D (2 * D)).product (Finset.Ico N (2 * N))).filter fun p =>
    0 < p.1 ∧ 0 < p.2 ∧ (p.1 : ℤ) ^ 2 ∣ (p.2 : ℤ) ^ 2 + a

/-- Exact membership in the shifted-square congruence-pair family. -/
@[simp] theorem mem_shiftedSquareCongruencePairs
    {a : ℤ} {D N d n : ℕ} :
    (d, n) ∈ shiftedSquareCongruencePairs a D N ↔
      0 < d ∧ 0 < n ∧ D ≤ d ∧ d < 2 * D ∧
        N ≤ n ∧ n < 2 * N ∧ (d : ℤ) ^ 2 ∣ (n : ℤ) ^ 2 + a := by
  classical
  simp only [shiftedSquareCongruencePairs, Finset.mem_filter]
  aesop

/-- Forget the uniquely determined squarefree coordinate `w`. -/
def shiftedSquareCongruenceProjection (p : ℕ × ℕ × ℕ) : ℕ × ℕ :=
  (p.1, p.2.2)

/-- Every shifted-square point projects to a congruence pair in the same
half-open `d` and `n` intervals. -/
theorem shiftedSquareCongruenceProjection_mem
    {a : ℤ} {D Y N : ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ shiftedSquareBlock a D Y N) :
    shiftedSquareCongruenceProjection p ∈
      shiftedSquareCongruencePairs a D N := by
  rcases p with ⟨d, w, n⟩
  obtain ⟨hd, _hw, hn, hdD, hdD', _hwY, _hwY', hnN, hnN', heq⟩ :=
    mem_shiftedSquareBlock.mp hp
  apply mem_shiftedSquareCongruencePairs.mpr
  refine ⟨hd, hn, hdD, hdD', hnN, hnN', ?_⟩
  refine ⟨(w : ℤ), ?_⟩
  simpa only [shiftedSquareCongruenceProjection] using heq.symm

/-- On a shifted-square block, the projection `(d,w,n) ↦ (d,n)` is
injective: positivity of `d` allows cancellation in the defining equation. -/
theorem shiftedSquareCongruenceProjection_injectiveOn
    {a : ℤ} {D Y N : ℕ} :
    Set.InjOn shiftedSquareCongruenceProjection
      {p : ℕ × ℕ × ℕ | p ∈ shiftedSquareBlock a D Y N} := by
  rintro ⟨d, w, n⟩ hp ⟨d', w', n'⟩ hp' hproj
  simp only [Set.mem_ofPred_eq] at hp hp'
  simp only [shiftedSquareCongruenceProjection, Prod.mk.injEq] at hproj
  obtain ⟨hdEq, hnEq⟩ := hproj
  subst d'
  subst n'
  have hmem := mem_shiftedSquareBlock.mp hp
  have hmem' := mem_shiftedSquareBlock.mp hp'
  have hdne : (d : ℤ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hmem.1))
  have hmul : (d : ℤ) ^ 2 * (w : ℤ) = (d : ℤ) ^ 2 * (w' : ℤ) :=
    hmem.2.2.2.2.2.2.2.2.2.trans hmem'.2.2.2.2.2.2.2.2.2.symm
  have hwCast : (w : ℤ) = (w' : ℤ) := mul_left_cancel₀ hdne hmul
  have hw : w = w' := Int.ofNat_inj.mp hwCast
  subst w'
  rfl

/-- Exact finite cardinality reduction from a shifted-square block to its
congruence-pair family. -/
theorem card_shiftedSquareBlock_le_congruencePairs
    {a : ℤ} {D Y N : ℕ} :
    (shiftedSquareBlock a D Y N).card ≤
      (shiftedSquareCongruencePairs a D N).card := by
  classical
  apply Finset.card_le_card_of_injOn shiftedSquareCongruenceProjection
  · intro p hp
    exact shiftedSquareCongruenceProjection_mem hp
  · intro p hp q hq hpq
    exact shiftedSquareCongruenceProjection_injectiveOn hp hq hpq

/-- The squarefree subblock satisfies the same congruence-pair reduction. -/
theorem card_squarefreeShiftedSquareBlock_le_congruencePairs
    {a : ℤ} {D Y N : ℕ} :
    (squarefreeShiftedSquareBlock a D Y N).card ≤
      (shiftedSquareCongruencePairs a D N).card := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    card_shiftedSquareBlock_le_congruencePairs

end

end PellPaper
