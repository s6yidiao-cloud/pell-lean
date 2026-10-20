import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Finite weighted rank filtrations

This file isolates the finite greedy-basis accounting used in the determinant
method.  For a finite linearly independent family with natural-number weights,
the total weight dominates the sum, over every integer layer, of the rank
deficit below that layer.  A separate corollary replaces the exact filtered
rank by any supplied rank cap.

The formulation is deliberately discrete.  It is intended to be applied to a
finite selected Taylor support (for example, the support produced by a
nonzero Cauchy--Binet minor), after real weights have been discretized or
grouped into finitely many layers.
-/

namespace PellPaper

open scoped BigOperators
open Finset

universe u v w

/-- Indices whose natural weight is at most the specified filtration level. -/
abbrev finiteWeightLowIndex {ι : Type u} (weight : ι → ℕ) (n : ℕ) :=
  {i : ι // weight i ≤ n}

/-- The span of the members of a family lying below one weight level. -/
noncomputable def finiteWeightFilteredSpan
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type u} (f : ι → V) (weight : ι → ℕ) (n : ℕ) :
    Submodule K V :=
  Submodule.span K (Set.range (fun i : finiteWeightLowIndex weight n => f i.1))

/-- A linearly independent finite family has at most the filtered-span rank
many members at every weight level. -/
theorem card_lowWeight_le_finrank_finiteWeightFilteredSpan
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℕ) (hlin : LinearIndependent K f) (n : ℕ) :
    ((Finset.univ.filter fun i => weight i ≤ n).card : ℕ) ≤
      Module.finrank K (finiteWeightFilteredSpan (K := K) f weight n) := by
  classical
  let g : finiteWeightLowIndex weight n →
      finiteWeightFilteredSpan (K := K) f weight n :=
    fun i => ⟨f i.1, by
      unfold finiteWeightFilteredSpan
      apply Submodule.subset_span
      exact ⟨i, rfl⟩⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp
      (finiteWeightFilteredSpan (K := K) f weight n).subtype
    change LinearIndependent K (fun i : finiteWeightLowIndex weight n => f i.1)
    exact hlin.comp (fun i : finiteWeightLowIndex weight n => i.1)
      Subtype.val_injective
  have hgcard := hg.fintype_card_le_finrank
  rw [Fintype.card_subtype] at hgcard
  exact hgcard

/-- The total natural weight dominates the number of elements above every
layer, summed through the finite range `0, ..., Q - 1`. -/
theorem sum_weight_ge_sum_highWeightLayerCards
    {ι : Type u} [Fintype ι] (weight : ι → ℕ) (Q : ℕ) :
    (∑ i, weight i) ≥
      ∑ n ∈ Finset.range Q,
        (Finset.univ.filter fun i => n < weight i).card := by
  classical
  have hsingle : ∀ i : ι,
      ((Finset.range Q).filter fun n => n < weight i).card ≤ weight i := by
    intro i
    calc
      ((Finset.range Q).filter fun n => n < weight i).card ≤
          (Finset.range (weight i)).card := by
        apply Finset.card_le_card
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      _ = weight i := Finset.card_range _
  have hsum :
      ∑ i, ((Finset.range Q).filter fun n => n < weight i).card ≤
        ∑ i, weight i :=
    Finset.sum_le_sum fun i _ => hsingle i
  calc
    ∑ n ∈ Finset.range Q,
        (Finset.univ.filter fun i => n < weight i).card =
        ∑ i, ((Finset.range Q).filter fun n => n < weight i).card := by
          simp_rw [Finset.card_filter]
          rw [Finset.sum_comm]
    _ ≤ ∑ i, weight i := hsum

/-- At one level, the number of selected vectors above that level is at least
the ambient cardinality minus the rank of the subfamily below it. -/
theorem card_sub_finrank_finiteWeightFilteredSpan_le_highWeightCard
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℕ) (hlin : LinearIndependent K f) (n : ℕ) :
    Fintype.card ι - Module.finrank K
      (finiteWeightFilteredSpan (K := K) f weight n) ≤
      (Finset.univ.filter fun i => n < weight i).card := by
  classical
  have hlow := card_lowWeight_le_finrank_finiteWeightFilteredSpan
    f weight hlin n
  have hpartition :
      (Finset.univ.filter fun i => weight i ≤ n).card +
        (Finset.univ.filter fun i => n < weight i).card = Fintype.card ι := by
    simpa [Nat.not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ι)) (p := fun i => weight i ≤ n))
  omega

/-- **Finite weighted rank-filtration bound.**  The total weight of a finite
linearly independent family is at least the sum of its filtered rank deficits
over any finite initial segment of weight levels. -/
theorem totalWeight_ge_rankFiltrationDeficit
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℕ) (hlin : LinearIndependent K f) (Q : ℕ) :
    (∑ i, weight i) ≥
      ∑ n ∈ Finset.range Q,
        (Fintype.card ι - Module.finrank K
          (finiteWeightFilteredSpan (K := K) f weight n)) := by
  have hlayers := sum_weight_ge_sum_highWeightLayerCards weight Q
  have hdeficit :
      (∑ n ∈ Finset.range Q,
          (Fintype.card ι - Module.finrank K
            (finiteWeightFilteredSpan (K := K) f weight n))) ≤
        (∑ n ∈ Finset.range Q,
          (Finset.univ.filter fun i => n < weight i).card) := by
    apply Finset.sum_le_sum
    intro n _
    exact card_sub_finrank_finiteWeightFilteredSpan_le_highWeightCard
      f weight hlin n
  exact hdeficit.trans hlayers

/-- The preceding weighted lower bound with a supplied finite rank cap in
place of the exact filtered rank.  This is the form used after a kernel or
parallel-line argument has bounded each filtration rank. -/
theorem totalWeight_ge_rankCapDeficit
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℕ) (rankCap : ℕ → ℕ)
    (hlin : LinearIndependent K f)
    (Q : ℕ)
    (hcap : ∀ n ∈ Finset.range Q,
      Module.finrank K (finiteWeightFilteredSpan (K := K) f weight n) ≤ rankCap n) :
    (∑ i, weight i) ≥
      ∑ n ∈ Finset.range Q, (Fintype.card ι - rankCap n) := by
  have hrank := totalWeight_ge_rankFiltrationDeficit (K := K) f weight hlin Q
  have hcapDeficit :
      (∑ n ∈ Finset.range Q, (Fintype.card ι - rankCap n)) ≤
        (∑ n ∈ Finset.range Q,
          (Fintype.card ι - Module.finrank K
            (finiteWeightFilteredSpan (K := K) f weight n))) := by
    apply Finset.sum_le_sum
    intro n hn
    have hncap := hcap n hn
    omega
  exact hcapDeficit.trans hrank

end PellPaper
