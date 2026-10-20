import Pell.FiniteRealWeightedRankFiltration

/-!
# Counting a linearly independent real-weight filtration

This module records the direct real-weight analogue of the low-layer count
lemma already available for natural weights.  It avoids rounding: the number
of selected independent vectors of weight at most a real threshold is at
most the dimension of their filtered span.
-/

namespace PellPaper

universe u v w

theorem card_le_finrank_finiteRealWeightFilteredSpan
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℝ) (hlin : LinearIndependent K f) (R : ℝ) :
    (Finset.univ.filter fun i => weight i ≤ R).card ≤
      Module.finrank K
        (finiteRealWeightFilteredSpan (K := K) f weight R) := by
  classical
  let g : {i : ι // weight i ≤ R} →
      finiteRealWeightFilteredSpan (K := K) f weight R :=
    fun i => ⟨f i.1, by
      unfold finiteRealWeightFilteredSpan
      apply Submodule.subset_span
      exact ⟨i, rfl⟩⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp
      (finiteRealWeightFilteredSpan (K := K) f weight R).subtype
    change LinearIndependent K (fun i : {i : ι // weight i ≤ R} => f i.1)
    exact hlin.comp (fun i : {i : ι // weight i ≤ R} => i.1)
      Subtype.val_injective
  have hgcard := hg.fintype_card_le_finrank
  rw [Fintype.card_subtype] at hgcard
  exact hgcard

end PellPaper
