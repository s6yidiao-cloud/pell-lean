import Pell.PrimeDivisorLogBound
import Pell.SquareSieveSquareFactor

/-!
# The square detector under a logarithmic bad-prime budget

The prime-divisor estimate discharges the finite detector's divisibility
hypothesis from a uniform absolute-value bound and a supplied prime-set
cardinality budget. The counted sets and ambient Jacobi correlations are
unchanged. No prime-distribution conclusion is asserted.
-/

open scoped BigOperators

namespace PellPaper

private theorem twice_card_filter_int_dvd_le_of_log_budget
    (P : Finset ℕ) (n : ℤ) (B W : ℝ) (hn : n ≠ 0) (hB : 1 < B)
    (hprime : ∀ p ∈ P, p.Prime) (hlower : ∀ p ∈ P, B ≤ (p : ℝ))
    (hsize : (n.natAbs : ℝ) ≤ W)
    (hbudget : 2 * Real.log W / Real.log B ≤ (P.card : ℝ)) :
    2 * (P.filter (fun p : ℕ => (p : ℤ) ∣ n)).card ≤ P.card := by
  have hnAbs : n.natAbs ≠ 0 := by simpa using hn
  have hnAbsPos : (0 : ℝ) < n.natAbs := by
    exact_mod_cast Nat.pos_of_ne_zero hnAbs
  have hcard := card_filter_int_dvd_le_log_div_log P n B hn hB hprime hlower
  have hlog := Real.log_le_log hnAbsPos hsize
  have hbound : ((P.filter (fun p : ℕ => (p : ℤ) ∣ n)).card : ℝ) ≤
      Real.log W / Real.log B :=
    hcard.trans (div_le_div_of_nonneg_right hlog (Real.log_pos hB).le)
  have htwice : 2 * ((P.filter (fun p : ℕ => (p : ℤ) ∣ n)).card : ℝ) ≤
      (P.card : ℝ) := by
    calc
      _ ≤ 2 * (Real.log W / Real.log B) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 2 * Real.log W / Real.log B := by ring
      _ ≤ _ := hbudget
  exact_mod_cast htwice

/-- A logarithmic size budget implies the finite detector for the literal
set of nonzero integer square values. -/
theorem squareSieve_logarithmic_detector
    {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset ℕ)
    (a : α → ℤ) (B W : ℝ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, p.Prime) (hB : 1 < B)
    (hlower : ∀ p ∈ P, B ≤ (p : ℝ))
    (hsize : ∀ x ∈ S, ((a x).natAbs : ℝ) ≤ W)
    (hbudget : 2 * Real.log W / Real.log B ≤ (P.card : ℝ)) :
    ((S.filter (fun x => a x ≠ 0 ∧ IsSquare (a x))).card : ℝ) ≤
      4 * (S.card : ℝ) / (P.card : ℝ) + 4 / (P.card : ℝ) ^ 2 *
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)| := by
  apply squareSieve_finite_detector S P a hP hprime
  intro x hx hn _
  exact twice_card_filter_int_dvd_le_of_log_budget P (a x) B W hn hB
    hprime hlower (hsize x hx) hbudget

/-- The same logarithmic bound on `f` detects its nonzero square values
while retaining full ambient correlations of `j` when `f = c*r^2*j`. -/
theorem squareSieve_logarithmic_detector_squareFactor
    {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset ℕ)
    (f r j : α → ℤ) (c : ℤ) (B W : ℝ)
    (hfactor : ∀ x ∈ S, f x = c * (r x) ^ 2 * j x)
    (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hc : ∀ p ∈ P, ¬ (p : ℤ) ∣ c) (hB : 1 < B)
    (hlower : ∀ p ∈ P, B ≤ (p : ℝ))
    (hsize : ∀ x ∈ S, ((f x).natAbs : ℝ) ≤ W)
    (hbudget : 2 * Real.log W / Real.log B ≤ (P.card : ℝ)) :
    ((S.filter (fun x => f x ≠ 0 ∧ IsSquare (f x))).card : ℝ) ≤
      4 * (S.card : ℝ) / (P.card : ℝ) + 4 / (P.card : ℝ) ^ 2 *
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)| := by
  apply squareSieve_finite_detector_squareFactor S P f r j c hfactor hP hprime hc
  intro x hx hn _
  exact twice_card_filter_int_dvd_le_of_log_budget P (f x) B W hn hB
    hprime hlower (hsize x hx) hbudget

end PellPaper
