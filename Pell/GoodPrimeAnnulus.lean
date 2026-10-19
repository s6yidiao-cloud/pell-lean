import Pell.PrimeAnnulusLowerBound
import Pell.PrimeDivisorLogBound

/-!
# A fourfold annulus avoiding a prescribed integer

For all sufficiently large `N`, the actual primes in `(N, 4N]` which do not
divide a nonzero integer `Delta` retain a fixed positive proportion, provided
`log |Delta|` is at most a fixed multiple of `N`. The threshold in `N` is
uniform in `Delta`.
-/

namespace PellPaper

/-- The literal prime annulus `(N, 4N]`, with the prime divisors of `Delta`
removed. -/
def goodPrimeAnnulus (N : ℕ) (Delta : ℤ) : Finset ℕ :=
  ((Finset.Ioc N (4 * N)).filter Nat.Prime).filter
    (fun p : ℕ => ¬ (p : ℤ) ∣ Delta)

/-- Uniformly in a nonzero integer of controlled logarithmic size, sufficiently
large fourfold annuli contain quantitatively many primes avoiding it. -/
theorem eventually_goodPrimeAnnulus_card_lower :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Delta : ℤ, Delta ≠ 0 →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
        (Real.log 2 / 8) * (N : ℝ) / Real.log (N : ℝ) ≤
          ((goodPrimeAnnulus N Delta).card : ℝ) := by
  filter_upwards [eventually_prime_annulus_card_lower,
    Filter.eventually_ge_atTop 4] with N hAnn hN
  intro Delta hDelta hDeltaSize
  let A := (Finset.Ioc N (4 * N)).filter Nat.Prime
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hprime (p : ℕ) (hp : p ∈ A) : p.Prime :=
    (Finset.mem_filter.mp hp).2
  have hlower (p : ℕ) (hp : p ∈ A) : (N : ℝ) ≤ p := by
    exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1.le
  have hbad₀ := card_filter_int_dvd_le_log_div_log A Delta (N : ℝ)
    hDelta (by linarith) hprime hlower
  have hbad :
      (((A.filter (fun p : ℕ => (p : ℤ) ∣ Delta)).card : ℝ)) ≤
        (Real.log 2 / 8) * (N : ℝ) / Real.log (N : ℝ) := by
    apply hbad₀.trans
    apply (div_le_iff₀ hlogN).2
    rw [div_mul_cancel₀ _ hlogN.ne']
    exact hDeltaSize
  have hsplitₙ := Finset.card_filter_add_card_filter_not
    (s := A) (p := fun p : ℕ => (p : ℤ) ∣ Delta)
  have hsplit :
      (((A.filter (fun p : ℕ => (p : ℤ) ∣ Delta)).card : ℝ)) +
          (((A.filter (fun p : ℕ => ¬ (p : ℤ) ∣ Delta)).card : ℝ)) =
        (A.card : ℝ) := by
    exact_mod_cast hsplitₙ
  change (Real.log 2 / 8) * (N : ℝ) / Real.log (N : ℝ) ≤
    (((A.filter (fun p : ℕ => ¬ (p : ℤ) ∣ Delta)).card : ℝ))
  change (Real.log 2 / 4) * (N : ℝ) / Real.log (N : ℝ) ≤
    (A.card : ℝ) at hAnn
  have htwice :
      (Real.log 2 / 4) * (N : ℝ) / Real.log (N : ℝ) =
        2 * ((Real.log 2 / 8) * (N : ℝ) / Real.log (N : ℝ)) := by
    ring
  rw [htwice] at hAnn
  linarith

/-- Under the same uniform size condition, the good-prime annulus is
eventually nonempty. This is the direct adapter required by the finite square
sieve. -/
theorem eventually_goodPrimeAnnulus_nonempty :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Delta : ℤ, Delta ≠ 0 →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
        (goodPrimeAnnulus N Delta).Nonempty := by
  filter_upwards [eventually_goodPrimeAnnulus_card_lower,
    Filter.eventually_ge_atTop 4] with N hcard hN
  intro Delta hDelta hDeltaSize
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hlower := hcard Delta hDelta hDeltaSize
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hpositive :
      0 < (Real.log 2 / 8) * (N : ℝ) / Real.log (N : ℝ) := by
    apply div_pos
    · exact mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num)) (by linarith)
    · exact Real.log_pos (by linarith)
  rw [hempty] at hlower
  simp only [Finset.card_empty, Nat.cast_zero] at hlower
  linarith

end PellPaper
