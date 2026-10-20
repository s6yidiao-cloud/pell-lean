import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite real-weight dominance from lower-level counts

This module isolates the order-statistics lemma used by minimum-weight-basis
arguments.  If one finite real-valued family has at least as many entries
below every threshold as another family of the same size, then its total
weight is no larger.
-/

namespace PellPaper

open scoped BigOperators

theorem card_filter_comp_perm_eq
    {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (R : ℝ) :
    (Finset.univ.filter fun i => w (σ i) ≤ R).card =
      (Finset.univ.filter fun i => w i ≤ R).card := by
  classical
  let e : {i : Fin n // i ∈ Finset.univ.filter fun i => w (σ i) ≤ R} ≃
      {i : Fin n // i ∈ Finset.univ.filter fun i => w i ≤ R} :=
    { toFun := fun i => ⟨σ i.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp i.2).2⟩
      invFun := fun i => ⟨σ.symm i.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using (Finset.mem_filter.mp i.2).2⟩
      left_inv := fun i => by
        apply Subtype.ext
        exact σ.symm_apply_apply i.1
      right_inv := fun i => by
        apply Subtype.ext
        exact σ.apply_symm_apply i.1 }
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr e

/-- Threshold-count dominance implies total-weight dominance. -/
theorem sum_le_sum_of_card_filter_le_card_filter
    {n : ℕ} (lighter heavier : Fin n → ℝ)
    (hcount : ∀ R : ℝ,
      (Finset.univ.filter fun i => heavier i ≤ R).card ≤
        (Finset.univ.filter fun i => lighter i ≤ R).card) :
    ∑ i, lighter i ≤ ∑ i, heavier i := by
  classical
  let lighterSorted : Fin n → ℝ := lighter ∘ Tuple.sort lighter
  let heavierSorted : Fin n → ℝ := heavier ∘ Tuple.sort heavier
  have hlighter_mono : Monotone lighterSorted := by
    exact Tuple.monotone_sort lighter
  have hheavier_mono : Monotone heavierSorted := by
    exact Tuple.monotone_sort heavier
  have hpoint : ∀ i, lighterSorted i ≤ heavierSorted i := by
    intro i
    let R := heavierSorted i
    have hi_heavier_sorted :
        i < (Finset.univ.filter fun j => heavierSorted j ≤ R).card :=
      (Tuple.lt_card_le_iff_apply_le_of_monotone hheavier_mono).mpr le_rfl
    have hi_heavier :
        i < (Finset.univ.filter fun j => heavier j ≤ R).card := by
      rw [← card_filter_comp_perm_eq heavier (Tuple.sort heavier) R]
      exact hi_heavier_sorted
    have hi_lighter :
        i < (Finset.univ.filter fun j => lighter j ≤ R).card :=
      hi_heavier.trans_le (hcount R)
    have hi_lighter_sorted :
        i < (Finset.univ.filter fun j => lighterSorted j ≤ R).card := by
      change i < (Finset.univ.filter fun j =>
        lighter ((Tuple.sort lighter) j) ≤ R).card
      rw [card_filter_comp_perm_eq lighter (Tuple.sort lighter) R]
      exact hi_lighter
    exact (Tuple.lt_card_le_iff_apply_le_of_monotone hlighter_mono).mp
      hi_lighter_sorted
  have hsum_sorted : (∑ i, lighterSorted i) ≤ ∑ i, heavierSorted i :=
    Finset.sum_le_sum fun i _ => hpoint i
  simpa [lighterSorted, heavierSorted, Equiv.sum_comp] using hsum_sorted

end PellPaper
