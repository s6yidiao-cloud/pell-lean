import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Weights of the standard two-layer basis

This file verifies the finite-sum calculation for `𝒲_{B,k}` in the proof of
`e:quantitative-two-layer-determinant` in `main.tex`. It does not assume or
assert the determinant estimate or the standard-basis theorem.
-/

namespace PellPaper

open Finset

/-- The sum of the real exponents `0, …, n`. -/
theorem sum_range_succ_natCast (n : ℕ) :
    (∑ i ∈ range (n + 1), (i : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

/-- The total weight of the standard monomials
`1, N₁, …, N₁^(B+k)` and `N₂, N₁*N₂, …, N₁^(B-k)*N₂`.
The real arguments stand for `log M` and `log X`. -/
noncomputable def twoLayerWeight (B k : ℕ) (logM logX : ℝ) : ℝ :=
  logM * ((∑ i ∈ range (B + k + 1), (i : ℝ)) +
    ∑ i ∈ range (B - k + 1), (i : ℝ)) + (B - k + 1 : ℕ) * logX

/-- The exact total-weight identity used in
`e:quantitative-two-layer-determinant`. -/
theorem twoLayerWeight_eq (B k : ℕ) (hk : k ≤ B) (logM logX : ℝ) :
    twoLayerWeight B k logM logX =
      (B : ℝ) * ((B : ℝ) + 1) * logM + ((B : ℝ) + 1) * logX -
        (k : ℝ) * logX + (k : ℝ) ^ 2 * logM := by
  unfold twoLayerWeight
  rw [sum_range_succ_natCast, sum_range_succ_natCast]
  push_cast [Nat.cast_sub hk]
  ring

/-- The two rows of monomial exponents in the standard basis. -/
def twoLayerBasisIndices (B k : ℕ) : Finset (ℕ × ℕ) :=
  ((range (B + k + 1)).image fun i => (i, 0)) ∪
    ((range (B - k + 1)).image fun i => (i, 1))

/-- The standard basis has `H = 2(B+1)` elements, independently of the
choice of the fan index `k ≤ B`. -/
theorem card_twoLayerBasisIndices (B k : ℕ) (hk : k ≤ B) :
    (twoLayerBasisIndices B k).card = 2 * (B + 1) := by
  have hdisj : Disjoint
      ((range (B + k + 1)).image fun i => (i, 0))
      ((range (B - k + 1)).image fun i => (i, 1)) := by
    apply disjoint_left.2
    intro p hp0 hp1
    obtain ⟨i, _, rfl⟩ := mem_image.1 hp0
    obtain ⟨j, _, hji⟩ := mem_image.1 hp1
    simp at hji
  unfold twoLayerBasisIndices
  rw [card_union_of_disjoint hdisj]
  have hinj0 : Function.Injective (fun i : ℕ => (i, (0 : ℕ))) :=
    fun _ _ h => (Prod.mk.inj h).1
  have hinj1 : Function.Injective (fun i : ℕ => (i, (1 : ℕ))) :=
    fun _ _ h => (Prod.mk.inj h).1
  rw [card_image_of_injective _ hinj0, card_image_of_injective _ hinj1,
    card_range, card_range]
  omega

end PellPaper
