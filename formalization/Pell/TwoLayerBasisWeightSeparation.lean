import Pell.TwoLayerBasisWeight
import Mathlib.Tactic

/-!
# Weight separation for the standard two-layer basis

This module proves the exact elementary ordering statement behind the fan
choice in the quantitative two-layer determinant argument.  When
`(2k-1) logM <= logX <= (2k+1) logM`, every monomial in the displayed
standard two-row basis has weight at most every omitted monomial in the
normal-form rows `j = 0,1`.

This is only the arithmetic ordering component.  Transporting an arbitrary
independent Taylor support to these normal-form rows is kept separate.
-/

namespace PellPaper

open Finset

theorem pair_mem_twoLayerBasisIndices_iff
    (B k i j : ℕ) :
    (i, j) ∈ twoLayerBasisIndices B k ↔
      (j = 0 ∧ i ≤ B + k) ∨ (j = 1 ∧ i ≤ B - k) := by
  simp only [twoLayerBasisIndices, mem_union, mem_image, mem_range,
    Prod.mk.injEq]
  aesop

theorem twoLayerMonomialWeight_le_firstRowBoundary
    (B k i : ℕ) (logM logX : ℝ) (hlogM : 0 ≤ logM)
    (hi : i ≤ B + k) :
    twoLayerMonomialWeight logM logX (i, 0) ≤
      (B + k : ℕ) * logM := by
  simp only [twoLayerMonomialWeight, Nat.cast_zero, zero_mul, add_zero]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hlogM

theorem twoLayerMonomialWeight_le_secondRowBoundary
    (B k i : ℕ) (logM logX : ℝ) (hlogM : 0 ≤ logM)
    (hi : i ≤ B - k) :
    twoLayerMonomialWeight logM logX (i, 1) ≤
      (B - k : ℕ) * logM + logX := by
  simp only [twoLayerMonomialWeight, Nat.cast_one, one_mul]
  have hi' : (i : ℝ) ≤ (B - k : ℕ) := by exact_mod_cast hi
  simpa [add_comm] using
    (add_le_add_right (mul_le_mul_of_nonneg_right hi' hlogM) logX)

theorem firstRowBoundary_le_twoLayerMonomialWeight_of_not_mem
    (B k i : ℕ) (logM logX : ℝ) (hlogM : 0 ≤ logM)
    (hi : (i, 0) ∉ twoLayerBasisIndices B k) :
    (B + k + 1 : ℕ) * logM ≤
      twoLayerMonomialWeight logM logX (i, 0) := by
  have hi' : B + k + 1 ≤ i := by
    rw [pair_mem_twoLayerBasisIndices_iff] at hi
    omega
  simp only [twoLayerMonomialWeight, Nat.cast_zero, zero_mul, add_zero]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi') hlogM

theorem secondRowBoundary_le_twoLayerMonomialWeight_of_not_mem
    (B k i : ℕ) (logM logX : ℝ) (hk : k ≤ B) (hlogM : 0 ≤ logM)
    (hi : (i, 1) ∉ twoLayerBasisIndices B k) :
    (B - k + 1 : ℕ) * logM + logX ≤
      twoLayerMonomialWeight logM logX (i, 1) := by
  have hi' : B - k + 1 ≤ i := by
    rw [pair_mem_twoLayerBasisIndices_iff] at hi
    omega
  simp only [twoLayerMonomialWeight, Nat.cast_one, one_mul]
  have hi'' : ((B - k + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi'
  simpa [add_comm] using
    (add_le_add_right (mul_le_mul_of_nonneg_right hi'' hlogM) logX)

theorem twoLayerBasisMonomialWeight_le_of_secondCoordinate_le_one
    (B k : ℕ) (hk : k ≤ B) (logM logX : ℝ)
    (hlogM : 0 ≤ logM)
    (hfanLower : ((2 * k : ℕ) : ℝ) * logM - logM ≤ logX)
    (hfanUpper : logX ≤ (((2 * k + 1 : ℕ) : ℝ) * logM))
    {p q : ℕ × ℕ}
    (hp : p ∈ twoLayerBasisIndices B k)
    (hqj : q.2 ≤ 1)
    (hq : q ∉ twoLayerBasisIndices B k) :
    twoLayerMonomialWeight logM logX p ≤
      twoLayerMonomialWeight logM logX q := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨u, v⟩
  rw [pair_mem_twoLayerBasisIndices_iff] at hp
  simp only at hqj
  interval_cases v
  · rcases hp with hp | hp
    · rcases hp with ⟨rfl, hi⟩
      exact (twoLayerMonomialWeight_le_firstRowBoundary
        B k i logM logX hlogM hi).trans
        ((show (B + k : ℕ) * logM ≤ (B + k + 1 : ℕ) * logM by
          have hcast : ((B + k : ℕ) : ℝ) ≤ (B + k + 1 : ℕ) := by
            exact_mod_cast Nat.le_succ (B + k)
          exact mul_le_mul_of_nonneg_right hcast hlogM).trans
          (firstRowBoundary_le_twoLayerMonomialWeight_of_not_mem
            B k u logM logX hlogM hq))
    · rcases hp with ⟨rfl, hi⟩
      refine (twoLayerMonomialWeight_le_secondRowBoundary
        B k i logM logX hlogM hi).trans ?_
      have hcross : (B - k : ℕ) * logM + logX ≤
          (B + k + 1 : ℕ) * logM := by
        push_cast [Nat.cast_sub hk] at hfanUpper ⊢
        nlinarith
      exact hcross.trans
        (firstRowBoundary_le_twoLayerMonomialWeight_of_not_mem
          B k u logM logX hlogM hq)
  · rcases hp with hp | hp
    · rcases hp with ⟨rfl, hi⟩
      refine (twoLayerMonomialWeight_le_firstRowBoundary
        B k i logM logX hlogM hi).trans ?_
      have hcross : (B + k : ℕ) * logM ≤
          (B - k + 1 : ℕ) * logM + logX := by
        push_cast [Nat.cast_sub hk] at hfanLower ⊢
        nlinarith
      exact hcross.trans
        (secondRowBoundary_le_twoLayerMonomialWeight_of_not_mem
          B k u logM logX hk hlogM hq)
    · rcases hp with ⟨rfl, hi⟩
      refine (twoLayerMonomialWeight_le_secondRowBoundary
        B k i logM logX hlogM hi).trans ?_
      have hstep : (B - k : ℕ) * logM + logX ≤
          (B - k + 1 : ℕ) * logM + logX := by
        have hcast : ((B - k : ℕ) : ℝ) ≤ (B - k + 1 : ℕ) := by
          exact_mod_cast Nat.le_succ (B - k)
        simpa [add_comm] using
          (add_le_add_right
            (mul_le_mul_of_nonneg_right hcast hlogM) logX)
      exact hstep.trans
        (secondRowBoundary_le_twoLayerMonomialWeight_of_not_mem
          B k u logM logX hk hlogM hq)

end PellPaper
