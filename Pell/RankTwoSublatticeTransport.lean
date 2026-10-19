import Pell.RankTwoSublatticeCounting

/-!
# Rank-two sublattice counting in arbitrary coordinates

A chosen `Fin 2`-indexed integer basis identifies an arbitrary rank-two
integer module with `Fin 2 → ℤ`.  This file transports the literal additive
subgroup index across that equivalence and then imports the finite counting
bound proved in standard coordinates.
-/

namespace PellPaper

open scoped BigOperators

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Passing a submodule to its coordinate image under an integer basis
preserves its literal additive-subgroup index, including index zero. -/
theorem index_map_basis_equivFun (b : Module.Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) :
    (N.map b.equivFun.toLinearMap).toAddSubgroup.index =
      N.toAddSubgroup.index := by
  rw [Submodule.map_toAddSubgroup]
  exact N.toAddSubgroup.index_map_equiv b.equivFun.toAddEquiv

/-- A chosen rank-two integer basis identifies the actual submodules of each
fixed additive-subgroup index with those in standard coordinates. -/
noncomputable def rankTwoSublatticesOfIndexEquiv
    (b : Module.Basis (Fin 2) ℤ M) (f : ℕ) :
    {N : Submodule ℤ M // N.toAddSubgroup.index = f} ≃
      {N : Submodule ℤ (Fin 2 → ℤ) // N.toAddSubgroup.index = f} := by
  let e : Submodule ℤ M ≃ Submodule ℤ (Fin 2 → ℤ) :=
    (Submodule.orderIsoMapComap b.equivFun).toEquiv
  exact e.subtypeEquiv fun N => by
    change N.toAddSubgroup.index = f ↔
      (N.map b.equivFun.toLinearMap).toAddSubgroup.index = f
    rw [index_map_basis_equivFun b N]

/-- There are finitely many submodules of a positive fixed index in any
integer module equipped with a `Fin 2`-indexed basis. -/
theorem finite_rankTwoSublatticesOfIndex_of_basis
    (b : Module.Basis (Fin 2) ℤ M) (f : ℕ) (hf : 0 < f) :
    Finite {N : Submodule ℤ M // N.toAddSubgroup.index = f} := by
  let _ := finite_rankTwoSublatticesOfIndex f hf
  exact Finite.of_injective (rankTwoSublatticesOfIndexEquiv b f)
    (rankTwoSublatticesOfIndexEquiv b f).injective

/-- At most `sigma₁(f)` submodules have positive index `f` in any integer
module equipped with a `Fin 2`-indexed basis. -/
theorem card_rankTwoSublatticesOfIndex_le_of_basis
    (b : Module.Basis (Fin 2) ℤ M) (f : ℕ) (hf : 0 < f) :
    Nat.card {N : Submodule ℤ M // N.toAddSubgroup.index = f} ≤
      ∑ a ∈ f.divisors, a := by
  calc
    Nat.card {N : Submodule ℤ M // N.toAddSubgroup.index = f} =
        Nat.card {N : Submodule ℤ (Fin 2 → ℤ) //
          N.toAddSubgroup.index = f} :=
      Nat.card_congr (rankTwoSublatticesOfIndexEquiv b f)
    _ ≤ ∑ a ∈ f.divisors, a := card_rankTwoSublatticesOfIndex_le f hf

end PellPaper
