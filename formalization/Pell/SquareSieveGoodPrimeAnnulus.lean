import Pell.GoodPrimeAnnulus
import Pell.SquareSieveLogarithmicDetector

/-!
# Feeding the uniform good-prime annulus into the square detector

One threshold in the sieve scale precedes the bad-reduction integer, content,
value bound, finite family, and all three integer-valued functions. The
prime-set cardinality, nonemptiness, lower endpoint, and avoidance of the
content are discharged from the actual annulus and the displayed logarithmic
budgets.
-/

open Filter
open scoped BigOperators

namespace PellPaper

/-- The literal logarithmic square-factor detector using the actual good
primes in `(N,4N]`. The conclusion still exposes the full ambient Jacobi
correlations; no correlation estimate is assumed or proved here. -/
theorem eventually_squareSieve_logarithmic_detector_squareFactor_goodPrimeAnnulus
    {α : Type*} [DecidableEq α] :
    ∀ᶠ N : ℕ in atTop, ∀ Delta c : ℤ, ∀ W : ℝ, ∀ S : Finset α,
      ∀ f r j : α → ℤ,
      Delta ≠ 0 → c ∣ Delta →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      (∀ x ∈ S, f x = c * (r x) ^ 2 * j x) →
      (∀ x ∈ S, ((f x).natAbs : ℝ) ≤ W) →
      ((S.filter (fun x => f x ≠ 0 ∧ IsSquare (f x))).card : ℝ) ≤
        4 * (S.card : ℝ) / ((goodPrimeAnnulus N Delta).card : ℝ) +
          4 / ((goodPrimeAnnulus N Delta).card : ℝ) ^ 2 *
            ∑ p ∈ goodPrimeAnnulus N Delta,
              ∑ q ∈ (goodPrimeAnnulus N Delta).erase p,
                |∑ x ∈ S, (jacobiSym (j x) p : ℝ) *
                  (jacobiSym (j x) q : ℝ)| := by
  filter_upwards [eventually_goodPrimeAnnulus_card_lower,
    eventually_goodPrimeAnnulus_nonempty, eventually_ge_atTop 4] with
      N hcard hnonempty hN
  intro Delta c W S f r j hDelta hcDelta hDeltaSize hW hfactor hsize
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hprime (p : ℕ) (hp : p ∈ goodPrimeAnnulus N Delta) : p.Prime := by
    rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
    exact (Finset.mem_filter.mp hp).2
  have hlower (p : ℕ) (hp : p ∈ goodPrimeAnnulus N Delta) :
      (N : ℝ) ≤ p := by
    rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
    exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1.le
  have hc (p : ℕ) (hp : p ∈ goodPrimeAnnulus N Delta) :
      ¬ (p : ℤ) ∣ c := by
    intro hpc
    exact (Finset.mem_filter.mp hp).2 (hpc.trans hcDelta)
  have hbudget : 2 * Real.log W / Real.log (N : ℝ) ≤
      ((goodPrimeAnnulus N Delta).card : ℝ) := by
    have htwice : 2 * Real.log W ≤ (Real.log 2 / 8) * (N : ℝ) := by
      nlinarith
    exact (div_le_div_of_nonneg_right htwice hlogN.le).trans
      (hcard Delta hDelta hDeltaSize)
  exact squareSieve_logarithmic_detector_squareFactor
    S (goodPrimeAnnulus N Delta) f r j c (N : ℝ) W hfactor
    (hnonempty Delta hDelta hDeltaSize) hprime hc (by linarith) hlower hsize hbudget

end PellPaper
