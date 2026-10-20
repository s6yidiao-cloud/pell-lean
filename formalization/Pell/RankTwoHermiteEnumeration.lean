import Pell.RankTwoHermiteIndex
import Mathlib.NumberTheory.Divisors

/-! A finite divisor-sized list of normalized index-`f` triangular lattices. -/

namespace PellPaper

open scoped BigOperators

/-- For each positive divisor `a` of `f`, list the `a` allowed upper entries.
At `f = 0` the list is empty; no infinite-index classification is asserted. -/
noncomputable def rankTwoHermiteEnumeration (f : ℕ) :
    Finset (Submodule ℤ (Fin 2 → ℤ)) := by
  classical
  exact f.divisors.biUnion fun a =>
    (Finset.range a).image fun b : ℕ => rankTwoHermiteSubmodule a b ((f / a : ℕ) : ℤ)

theorem mem_rankTwoHermiteEnumeration_iff (f : ℕ) (N : Submodule ℤ (Fin 2 → ℤ)) :
    N ∈ rankTwoHermiteEnumeration f ↔
      ∃ a ∈ f.divisors, ∃ b : ℕ, b < a ∧
        N = rankTwoHermiteSubmodule a b ((f / a : ℕ) : ℤ) := by
  classical
  simp only [rankTwoHermiteEnumeration, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, hN⟩
    exact ⟨a, ha, b, hb, hN.symm⟩
  · rintro ⟨a, ha, b, hb, hN⟩
    exact ⟨a, ha, b, hb, hN.symm⟩

theorem card_rankTwoHermiteEnumeration_le (f : ℕ) :
    (rankTwoHermiteEnumeration f).card ≤ ∑ a ∈ f.divisors, a := by
  classical
  unfold rankTwoHermiteEnumeration
  calc
    _ ≤ ∑ a ∈ f.divisors,
        ((Finset.range a).image fun b : ℕ =>
          rankTwoHermiteSubmodule a b ((f / a : ℕ) : ℤ)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ f.divisors, a := Finset.sum_le_sum fun a _ =>
      (Finset.card_image_le).trans (by simp)

theorem index_eq_of_mem_rankTwoHermiteEnumeration (f : ℕ)
    (N : Submodule ℤ (Fin 2 → ℤ)) (hN : N ∈ rankTwoHermiteEnumeration f) :
    N.toAddSubgroup.index = f := by
  obtain ⟨a, ha, b, _, rfl⟩ := (mem_rankTwoHermiteEnumeration_iff f N).mp hN
  have ha0 := Nat.pos_of_mem_divisors ha
  have hf0 := Nat.ne_zero_of_mem_divisors ha
  have had : a * (f / a) = f := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
  have hd : 0 < f / a := by
    by_contra h
    have : f / a = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at had
    exact hf0 had.symm
  rw [index_rankTwoHermiteSubmodule_nat a b (f / a) ha0 hd, had]

theorem mem_rankTwoHermiteEnumeration_of_normalized (f a b d : ℕ)
    (hf : 0 < f) (hb : b < a) (hprod : a * d = f) :
    rankTwoHermiteSubmodule a b d ∈ rankTwoHermiteEnumeration f := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.zero_le b) hb
  have hdiv : f / a = d := by
    rw [← hprod, Nat.mul_div_cancel_left d ha]
  apply (mem_rankTwoHermiteEnumeration_iff f _).mpr
  exact ⟨a, Nat.mem_divisors.mpr ⟨⟨d, hprod.symm⟩, Nat.ne_of_gt hf⟩,
    b, hb, by rw [hdiv]⟩

end PellPaper
