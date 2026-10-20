import Pell.PointwiseEliminantProjection
import Pell.ShiftedSquareReduction

/-!
# Finite primitive projection across the four signed surface levels

An actual mixed-level source-target family is partitioned by the literal
surface value. Each nonzero level has its own eliminant. The final bound
counts target vectors where those four eliminants evaluate to nonzero
squares; it does not count distinct integer square values.

The common-target zero branch is retained once before this partition.
No dyadic representation, coordinate-height budget or analytic estimate
is asserted in this finite algebraic module.
-/

namespace PellPaper
noncomputable section
open scoped BigOperators

/-- A mixed signed-level family projects to the sum of four actual
nonzero-square target filters, with multiplicity at most two per level. -/
theorem card_signed_surface_solutions_le_two_mul_sum_squares
    (g : Fin 3 → Fin 2 → ℤ) (A B : MvPolynomial (Fin 2) ℤ)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      p.1 0 * MvPolynomial.eval p.2 A + p.1 1 * MvPolynomial.eval p.2 B = 0 ∧
      IsSignedDyadicDifference (quadraticLinearFormEval g p.1 p.2))
    (hcomponents : ∀ p ∈ S, MvPolynomial.eval p.2 A ≠ 0 ∨ MvPolynomial.eval p.2 B ≠ 0)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ 2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
      (T.filter fun y =>
        IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g h A B)) ∧
          MvPolynomial.eval y (quadraticLinearEliminant g h A B) ≠ 0).card := by
  classical
  let level := fun p : (Fin 2 → ℤ) × (Fin 2 → ℤ) =>
    quadraticLinearFormEval g p.1 p.2
  have hmap : (S : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ))).MapsTo level
      ({1, -1, 2, -2} : Finset ℤ) := by
    intro p hp
    simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      IsSignedDyadicDifference] using (hS p hp).2.2.2
  calc
    S.card = ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        (S.filter fun p => level p = h).card := Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        2 * (T.filter fun y =>
          IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g h A B)) ∧
            MvPolynomial.eval y (quadraticLinearEliminant g h A B) ≠ 0).card := by
      apply Finset.sum_le_sum
      intro h hh
      have hs : IsSignedDyadicDifference h := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, IsSignedDyadicDifference] using hh
      apply card_primitive_surface_solutions_le_two_mul_squares_of_component_nonvanishing
        g h A B (isSignedDyadicDifference_ne_zero hs)
      · intro p hp
        obtain ⟨hpS, hpLevel⟩ := Finset.mem_filter.mp hp
        exact ⟨(hS p hpS).1, (hS p hpS).2.1, (hS p hpS).2.2.1, hpLevel⟩
      · intro p hp
        exact hcomponents p (Finset.mem_filter.mp hp).1
      · intro p hp
        exact hT p (Finset.mem_filter.mp hp).1
    _ = _ := (Finset.mul_sum ..).symm

/-- Retain common-target zeros once, then project the residual branch
over all four distinct signed-level eliminants. -/
theorem card_signed_surface_solutions_le_common_factor_zeros_add_twice_sum_squares
    (g : Fin 3 → Fin 2 → ℤ) (A₀ B₀ D A B : MvPolynomial (Fin 2) ℤ)
    (hA : A₀ = D * A) (hB : B₀ = D * B)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      p.1 0 * MvPolynomial.eval p.2 A₀ + p.1 1 * MvPolynomial.eval p.2 B₀ = 0 ∧
      IsSignedDyadicDifference (quadraticLinearFormEval g p.1 p.2))
    (hcomponents : ∀ p ∈ S, MvPolynomial.eval p.2 D ≠ 0 →
      MvPolynomial.eval p.2 A ≠ 0 ∨ MvPolynomial.eval p.2 B ≠ 0)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ (S.filter fun p => MvPolynomial.eval p.2 D = 0).card +
      2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        (T.filter fun y =>
          IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g h A B)) ∧
            MvPolynomial.eval y (quadraticLinearEliminant g h A B) ≠ 0).card := by
  classical
  let U := S.filter fun p => MvPolynomial.eval p.2 D ≠ 0
  have hU := card_signed_surface_solutions_le_two_mul_sum_squares g A B U T (by
    intro p hp
    obtain ⟨hpS, hpD⟩ := Finset.mem_filter.mp hp
    refine ⟨(hS p hpS).1, (hS p hpS).2.1, ?_, (hS p hpS).2.2.2⟩
    exact ((source_linear_zero_iff_common_factor_or_residual
      A₀ B₀ D A B hA hB p.1 p.2).mp (hS p hpS).2.2.1).resolve_left hpD)
    (by
      intro p hp
      obtain ⟨hpS, hpD⟩ := Finset.mem_filter.mp hp
      exact hcomponents p hpS hpD)
    (by intro p hp; exact hT p (Finset.mem_filter.mp hp).1)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun p => MvPolynomial.eval p.2 D = 0)
  change (S.filter fun p => MvPolynomial.eval p.2 D = 0).card + U.card = S.card
    at hpartition
  omega

end
end PellPaper
