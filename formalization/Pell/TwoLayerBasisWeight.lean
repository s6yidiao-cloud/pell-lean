import Pell.TwoLayerWeights

/-!
# The actual weight of the two-layer standard basis

`TwoLayerWeights` verifies the closed formula for the determinant weight in
`e:quantitative-two-layer-determinant` of `main.tex`.  This module connects
that formula to the literal sum of the weights of the monomials in
`twoLayerBasisIndices`, so the bookkeeping uses the same finite basis as the
linear-independence and interpolation developments.

No determinant estimate is asserted here.
-/

namespace PellPaper

open Finset

/-- The local determinant weight of the monomial with exponent pair `(i, j)`.
The arguments stand for `log M` and `log X`, respectively. -/
noncomputable def twoLayerMonomialWeight (logM logX : ℝ) (ij : ℕ × ℕ) : ℝ :=
  (ij.1 : ℝ) * logM + (ij.2 : ℝ) * logX

/-- The literal sum of the monomial weights in `twoLayerBasisIndices` is the
weight ledger `twoLayerWeight`.  This identity is valid even when `k > B`;
the later fan application supplies `k ≤ B`. -/
theorem sum_twoLayerBasisMonomialWeight_eq_twoLayerWeight
    (B k : ℕ) (logM logX : ℝ) :
    ∑ ij ∈ twoLayerBasisIndices B k, twoLayerMonomialWeight logM logX ij =
      twoLayerWeight B k logM logX := by
  have hdisj : Disjoint
      ((range (B + k + 1)).image fun i => (i, 0))
      ((range (B - k + 1)).image fun i => (i, 1)) := by
    apply disjoint_left.2
    intro p hp0 hp1
    obtain ⟨i, _, rfl⟩ := mem_image.1 hp0
    obtain ⟨j, _, hji⟩ := mem_image.1 hp1
    simp at hji
  unfold twoLayerBasisIndices
  rw [sum_union hdisj]
  have hinj0 : Set.InjOn (fun i : ℕ => (i, (0 : ℕ)))
      ↑(range (B + k + 1)) := by
    intro i hi j hj hij
    exact (Prod.mk.inj hij).1
  have hinj1 : Set.InjOn (fun i : ℕ => (i, (1 : ℕ)))
      ↑(range (B - k + 1)) := by
    intro i hi j hj hij
    exact (Prod.mk.inj hij).1
  rw [Finset.sum_image hinj0, Finset.sum_image hinj1]
  simp only [twoLayerMonomialWeight, Nat.cast_zero, zero_mul, add_zero,
    Nat.cast_one, one_mul]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  unfold twoLayerWeight
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The literal basis-weight sum has the exact closed form used in the
two-layer determinant exponent, under the fan range `k ≤ B`. -/
theorem sum_twoLayerBasisMonomialWeight_eq
    (B k : ℕ) (hk : k ≤ B) (logM logX : ℝ) :
    ∑ ij ∈ twoLayerBasisIndices B k, twoLayerMonomialWeight logM logX ij =
      (B : ℝ) * ((B : ℝ) + 1) * logM + ((B : ℝ) + 1) * logX -
        (k : ℝ) * logX + (k : ℝ) ^ 2 * logM := by
  rw [sum_twoLayerBasisMonomialWeight_eq_twoLayerWeight,
    twoLayerWeight_eq B k hk]

end PellPaper
