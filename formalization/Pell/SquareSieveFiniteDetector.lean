import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The finite quadratic-character square detector

The accepted set is explicit: in the polynomial application the accepted
values are squares of `f`, while the character is evaluated on its squarefree
part times its content. Correlations below are literal Jacobi-symbol sums.
-/

open scoped BigOperators

namespace PellPaper

theorem jacobiSym_of_isSquare_at_prime (a : ℤ) (ha : IsSquare a)
    (p : ℕ) (hp : p.Prime) :
    jacobiSym a p = if (p : ℤ) ∣ a then 0 else 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  split_ifs with h
  · exact (legendreSym.eq_zero_iff p a).2
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).2 h)
  · exact (legendreSym.eq_one_iff p (by
      intro haz
      exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 haz))).2
      (ha.map (Int.castRingHom (ZMod p)))

private theorem jacobiSym_real_sq_le_one (a : ℤ) (p : ℕ) :
    (jacobiSym a p : ℝ) ^ 2 ≤ 1 := by
  rcases jacobiSym.trichotomy a p with h | h | h <;> rw [h] <;> norm_num

/-- A square sieve with an arbitrary accepted subset and actual character
correlations. At least half the selected primes must not divide an accepted
value; no cancellation estimate is assumed or hidden in the conclusion. -/
theorem squareSieve_finite_detector_subset
    {α : Type*} [DecidableEq α] (S A : Finset α) (P : Finset ℕ)
    (a : α → ℤ) (hAS : A ⊆ S) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, p.Prime) (hsquare : ∀ x ∈ A, IsSquare (a x))
    (hbad : ∀ x ∈ A,
      2 * (P.filter (fun p : ℕ => (p : ℤ) ∣ a x)).card ≤ P.card) :
    (A.card : ℝ) ≤ 4 * (S.card : ℝ) / (P.card : ℝ) +
      4 / (P.card : ℝ) ^ 2 *
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)| := by
  have hR : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hpoint (x : α) (hx : x ∈ A) :
      (P.card : ℝ) ^ 2 ≤ 4 * (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) ^ 2 := by
    have hid : (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) +
        ((P.filter (fun p : ℕ => (p : ℤ) ∣ a x)).card : ℝ) = P.card := by
      rw [Finset.card_filter]
      push_cast
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ _p ∈ P, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [jacobiSym_of_isSquare_at_prime (a x) (hsquare x hx) p (hprime p hp)]
          by_cases h : (p : ℤ) ∣ a x <;> simp [h]
        _ = _ := by simp
    have hb : 2 * ((P.filter (fun p : ℕ => (p : ℤ) ∣ a x)).card : ℝ) ≤ P.card :=
      by exact_mod_cast hbad x hx
    have hsum : (P.card : ℝ) ≤ 2 * ∑ p ∈ P, (jacobiSym (a x) p : ℝ) := by
      linarith
    nlinarith [sq_nonneg ((∑ p ∈ P, (jacobiSym (a x) p : ℝ)) - P.card / 2)]
  have hlower : (P.card : ℝ) ^ 2 * A.card ≤
      4 * ∑ x ∈ S, (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) ^ 2 := by
    calc
      _ = ∑ _x ∈ A, (P.card : ℝ) ^ 2 := by simp [mul_comm]
      _ ≤ ∑ x ∈ A, 4 * (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) ^ 2 :=
        Finset.sum_le_sum hpoint
      _ = 4 * ∑ x ∈ A, (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) ^ 2 :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hAS (by intros; positivity)) (by norm_num)
  have hexpand : (∑ x ∈ S, (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, ∑ x ∈ S,
        (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ) := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  have hupper : (∑ x ∈ S, (∑ p ∈ P, (jacobiSym (a x) p : ℝ)) ^ 2) ≤
      (P.card : ℝ) * S.card +
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)| := by
    rw [hexpand]
    calc
      _ ≤ ∑ p ∈ P, ((S.card : ℝ) + ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)|) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [← Finset.sum_erase_add _ _ hp]
        have hdiag : (∑ x ∈ S,
            (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) p : ℝ)) ≤ S.card := by
          calc
            _ ≤ ∑ _x ∈ S, (1 : ℝ) := Finset.sum_le_sum (by
              intro x _; simpa only [← pow_two] using jacobiSym_real_sq_le_one (a x) p)
            _ = _ := by simp
        have hoff := Finset.sum_le_sum (s := P.erase p) (fun q _ =>
          le_abs_self (∑ x ∈ S,
            (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)))
        linarith
      _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_comm]
  have htotal := hlower.trans (mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 4))
  calc
    _ ≤ (4 * ((P.card : ℝ) * S.card +
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)|)) /
        (P.card : ℝ) ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hR)).2 (by simpa [mul_comm] using htotal)
    _ = _ := by field_simp

/-- The exact finite set of nonzero integer squares satisfies the detector. -/
theorem squareSieve_finite_detector
    {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset ℕ)
    (a : α → ℤ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hbad : ∀ x ∈ S, a x ≠ 0 → IsSquare (a x) →
      2 * (P.filter (fun p : ℕ => (p : ℤ) ∣ a x)).card ≤ P.card) :
    ((S.filter (fun x => a x ≠ 0 ∧ IsSquare (a x))).card : ℝ) ≤
      4 * (S.card : ℝ) / (P.card : ℝ) + 4 / (P.card : ℝ) ^ 2 *
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (a x) p : ℝ) * (jacobiSym (a x) q : ℝ)| := by
  apply squareSieve_finite_detector_subset S _ P a (Finset.filter_subset ..) hP hprime
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.2
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, hn, hs⟩
    exact hbad x hx hn hs

end PellPaper
