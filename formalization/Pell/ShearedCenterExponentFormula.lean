import Pell.ShearedEvaluationMatrixTransport

/-!
# Closed centre exponent for the sheared bidegree determinant

The local-column transport extracts the factor `s₀^(a + 2b)` from each
standard bidegree column.  This file evaluates the resulting finite exponent
sum, giving the exact centre exponent used in the determinant bookkeeping of
`L:sheared` in `main.tex`.

It is a finite arithmetic identity only; it does not estimate a determinant.
-/

namespace PellPaper

open scoped BigOperators

/-- The sum of the values in `Fin (n + 1)`. -/
theorem sum_fin_succ_val (n : ℕ) :
    ∑ i : Fin (n + 1), i.1 = n * (n + 1) / 2 := by
  calc
    ∑ i : Fin (n + 1), i.1 = ∑ i ∈ Finset.range (n + 1), i := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = n * (n + 1) / 2 := by
      simpa [Nat.succ_sub_one, Nat.mul_comm] using Finset.sum_range_id (n + 1)

/-- A constant summed over `Fin (n + 1)`. -/
theorem sum_fin_succ_const (n c : ℕ) :
    ∑ _ : Fin (n + 1), c = (n + 1) * c := by
  simp [Nat.mul_comm]

/-- The closed form for the total centre exponent over all bidegree columns. -/
theorem shearedCenterExponent_eq (A B : ℕ) :
    shearedCenterExponent A B =
      (B + 1) * (A * (A + 1) / 2) + (A + 1) * (B * (B + 1)) := by
  have hinner (a : Fin (A + 1)) :
      (∑ b : Fin (B + 1), (a.1 + 2 * b.1)) =
        (B + 1) * a.1 + 2 * (B * (B + 1) / 2) := by
    rw [Finset.sum_add_distrib, sum_fin_succ_const]
    rw [← Finset.mul_sum, sum_fin_succ_val]
  unfold shearedCenterExponent
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_fin_succ_val,
    sum_fin_succ_const]
  rw [Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self B)]

/-- Equivalently, the centre exponent is the manuscript's
`(A+1)(B+1)(A+2B)/2`. -/
theorem shearedCenterExponent_eq_card_mul_shearedDegree_div_two (A B : ℕ) :
    shearedCenterExponent A B =
      ((A + 1) * (B + 1) * (A + 2 * B)) / 2 := by
  have hA : 2 * (A * (A + 1) / 2) = A * (A + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self A)
  have htwice : 2 * shearedCenterExponent A B =
      (A + 1) * (B + 1) * (A + 2 * B) := by
    rw [shearedCenterExponent_eq]
    calc
      2 * ((B + 1) * (A * (A + 1) / 2) +
          (A + 1) * (B * (B + 1))) =
          (B + 1) * (2 * (A * (A + 1) / 2)) +
            (A + 1) * (B + 1) * (2 * B) := by ring
      _ = (A + 1) * (B + 1) * (A + 2 * B) := by
        rw [hA]
        ring
  have hdiv : 2 ∣ (A + 1) * (B + 1) * (A + 2 * B) :=
    ⟨shearedCenterExponent A B, htwice.symm⟩
  symm
  exact (Nat.div_eq_iff_eq_mul_right (by norm_num) hdiv).mpr htwice.symm

/-- The complete product of local centre-column factors in the closed
form used by the sheared determinant calculation. -/
theorem prod_shearedCenterColumnScale_eq_card_mul_shearedDegree_div_two
    (A B : ℕ) (s₀ : ℝ) :
    ∏ ab : generalBidegreeFormIndex A B,
      shearedCenterColumnScale (A := A) (B := B) s₀ ab =
        s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) := by
  rw [prod_shearedCenterColumnScale,
    shearedCenterExponent_eq_card_mul_shearedDegree_div_two]

end PellPaper
