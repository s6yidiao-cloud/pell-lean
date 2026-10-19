import Pell.DivisorCountSubpower
import Pell.AuxiliaryParabolaDivisorCounting

/-!
# A genuine subpower bound for the special-parabola denominator gate

The actual positive denominator pairs satisfying `e^2 * u ∣ n` lie in the
Cartesian product of the actual divisor sets.  The unconditional divisor
estimate, with exponent halved, therefore bounds this gate by every positive
real power.  No divisor bound, pair capacity, or curve count is a premise.
-/

namespace PellPaper

/-- Both coordinates of an actual denominator pair divide the nonzero input. -/
theorem specialParabolaDenominatorPairs_subset_divisors_product
    {n : ℕ} (hn : n ≠ 0) :
    specialParabolaDenominatorPairs n ⊆ n.divisors ×ˢ n.divisors := by
  rintro ⟨e, u⟩ hmem
  rcases (mem_specialParabolaDenominatorPairs_iff hn).mp hmem with ⟨_he, _hu, hdiv⟩
  apply Finset.mem_product.mpr
  constructor
  · apply Nat.mem_divisors.mpr
    exact ⟨dvd_trans (dvd_mul_of_dvd_left (dvd_pow_self e (by decide : 2 ≠ 0)) u)
      hdiv, hn⟩
  · exact Nat.mem_divisors.mpr ⟨dvd_trans (dvd_mul_left u (e ^ 2)) hdiv, hn⟩

/-- The denominator gate is bounded by the square of the actual divisor count. -/
theorem card_specialParabolaDenominatorPairs_le_sq_card_divisors
    {n : ℕ} (hn : n ≠ 0) :
    (specialParabolaDenominatorPairs n).card ≤ n.divisors.card ^ 2 := by
  calc
    (specialParabolaDenominatorPairs n).card ≤ (n.divisors ×ˢ n.divisors).card :=
      Finset.card_le_card (specialParabolaDenominatorPairs_subset_divisors_product hn)
    _ = n.divisors.card ^ 2 := by rw [Finset.card_product, pow_two]

/-- Every positive real power bounds the actual denominator gate uniformly. -/
theorem exists_pos_card_specialParabolaDenominatorPairs_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((specialParabolaDenominatorPairs n).card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_card_divisors_le_rpow (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC _, ?_⟩
  intro n hn
  have hgate : ((specialParabolaDenominatorPairs n).card : ℝ) ≤
      (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast card_specialParabolaDenominatorPairs_le_sq_card_divisors (ne_of_gt hn)
  calc
    ((specialParabolaDenominatorPairs n).card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := hgate
    _ ≤ (C * (n : ℝ) ^ (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hbound n hn) 2
    _ = C ^ 2 * (n : ℝ) ^ ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      congr 2
      norm_num

end PellPaper
