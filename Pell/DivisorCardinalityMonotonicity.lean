import Mathlib.NumberTheory.Divisors

/-!
# Monotonicity of the divisor-counting function under divisibility

The positive divisors of a natural divisor form a subset of the positive
divisors of any nonzero multiple.  We record the cardinality consequence for
naturals, integer absolute values, and an exact integer quotient.  The last
form is the small arithmetic step `tau(|c/g|) <= tau(|c|)` in
the manuscript.
-/

namespace PellPaper

/-- Divisor count is monotone under divisibility when the upper integer is
nonzero. -/
theorem card_divisors_le_card_divisors_of_dvd
    {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    m.divisors.card ≤ n.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hn hmn)

/-- The corresponding monotonicity statement for absolute values of
integers. -/
theorem card_divisors_natAbs_le_card_divisors_natAbs_of_dvd
    {m n : ℤ} (hn : n ≠ 0) (hmn : m ∣ n) :
    m.natAbs.divisors.card ≤ n.natAbs.divisors.card := by
  apply card_divisors_le_card_divisors_of_dvd
    (Int.natAbs_ne_zero.mpr hn)
  exact Int.natAbs_dvd_natAbs.mpr hmn

/-- If `g` divides a nonzero integer `c`, then the divisor count of the exact
quotient `c/g` is at most the divisor count of `c`. -/
theorem card_divisors_natAbs_ediv_le_card_divisors_natAbs_of_dvd
    {g c : ℤ} (hc : c ≠ 0) (hgc : g ∣ c) :
    (c / g).natAbs.divisors.card ≤ c.natAbs.divisors.card := by
  apply card_divisors_natAbs_le_card_divisors_natAbs_of_dvd hc
  refine ⟨g, ?_⟩
  exact (Int.ediv_mul_cancel hgc).symm

end PellPaper
