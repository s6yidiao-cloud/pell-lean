import Pell.RankTwoHermiteClassification
import Pell.RankTwoHermiteEnumeration

/-! The actual family of index-`f` sublattices of `ℤ²` is divisor-sum bounded. -/

namespace PellPaper

open scoped BigOperators

theorem mem_rankTwoHermiteEnumeration_iff_index (f : ℕ) (hf : 0 < f)
    (N : Submodule ℤ (Fin 2 → ℤ)) :
    N ∈ rankTwoHermiteEnumeration f ↔ N.toAddSubgroup.index = f := by
  constructor
  · exact index_eq_of_mem_rankTwoHermiteEnumeration f N
  · intro hN
    have hN0 : N.toAddSubgroup.index ≠ 0 := by rw [hN]; exact Nat.ne_of_gt hf
    obtain ⟨a, d, ha, hd, b, hb, rfl⟩ :=
      exists_rankTwoHermiteSubmodule_of_index_ne_zero N hN0
    have hprod : a * d = f := by
      rw [index_rankTwoHermiteSubmodule_nat a b d ha hd] at hN
      exact hN
    exact mem_rankTwoHermiteEnumeration_of_normalized f a b d hf hb hprod

/-- Finiteness is separate from `Nat.card`, whose infinite-type convention is zero. -/
theorem finite_rankTwoSublatticesOfIndex (f : ℕ) (hf : 0 < f) :
    Finite {N : Submodule ℤ (Fin 2 → ℤ) // N.toAddSubgroup.index = f} := by
  let e : {N : Submodule ℤ (Fin 2 → ℤ) // N.toAddSubgroup.index = f} →
      ↥(rankTwoHermiteEnumeration f) := fun N =>
    ⟨N.1, (mem_rankTwoHermiteEnumeration_iff_index f hf N.1).mpr N.2⟩
  exact Finite.of_injective e fun N M h =>
    Subtype.ext (congrArg (fun S : ↥(rankTwoHermiteEnumeration f) => S.1) h)

/-- At most `sigma₁(f)` actual rank-two integer sublattices have positive index `f`. -/
theorem card_rankTwoSublatticesOfIndex_le (f : ℕ) (hf : 0 < f) :
    Nat.card {N : Submodule ℤ (Fin 2 → ℤ) // N.toAddSubgroup.index = f} ≤
      ∑ a ∈ f.divisors, a := by
  let e : {N : Submodule ℤ (Fin 2 → ℤ) // N.toAddSubgroup.index = f} →
      ↥(rankTwoHermiteEnumeration f) := fun N =>
    ⟨N.1, (mem_rankTwoHermiteEnumeration_iff_index f hf N.1).mpr N.2⟩
  calc
    _ ≤ Nat.card ↥(rankTwoHermiteEnumeration f) :=
      Nat.card_le_card_of_injective e fun N M h =>
        Subtype.ext (congrArg (fun S : ↥(rankTwoHermiteEnumeration f) => S.1) h)
    _ = (rankTwoHermiteEnumeration f).card := Nat.card_eq_finsetCard _
    _ ≤ ∑ a ∈ f.divisors, a := card_rankTwoHermiteEnumeration_le f

end PellPaper
