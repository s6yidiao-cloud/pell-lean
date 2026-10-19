import Pell.SquareSieveFiniteDetector
import Mathlib.Data.Rat.Lemmas

/-!
# Removing an integer square factor from the finite square sieve

The counted set remains the nonzero square values of `f`, while the full
ambient correlations use `j` when `f = c*r^2*j`. No condition is imposed on
the removed factor away from the accepted points.
-/

open scoped BigOperators

namespace PellPaper

theorem isSquare_of_isSquare_mul_sq_int (b r : ℤ) (hr : r ≠ 0)
    (h : IsSquare (b * r ^ 2)) : IsSquare b := by
  apply Rat.isSquare_intCast_iff.mp
  have hq : IsSquare ((b : ℚ) * (r : ℚ) ^ 2) := by
    have hcast : IsSquare ((b * r ^ 2 : ℤ) : ℚ) := Rat.isSquare_intCast_iff.mpr h
    simpa only [Int.cast_mul, Int.cast_pow] using hcast
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr
  simpa only [mul_div_cancel_right₀ _ (pow_ne_zero 2 hrq)] using
    hq.div (IsSquare.sq (r : ℚ))

private theorem abs_jacobiSym_at_prime_eq_one (c : ℤ) (p : ℕ)
    (hp : p.Prime) (hc : ¬ (p : ℤ) ∣ c) : |(jacobiSym c p : ℝ)| = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hn : jacobiSym c p ≠ 0 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    intro hz
    exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).1
      ((legendreSym.eq_zero_iff p c).1 hz))
  rcases jacobiSym.trichotomy c p with h | h | h
  · exact (hn h).elim
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- Exact constant-factor removal in the full ambient correlation. -/
theorem abs_sum_jacobiSym_const_mul_correlation
    {α : Type*} (S : Finset α) (j : α → ℤ) (c : ℤ) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime)
    (hcp : ¬ (p : ℤ) ∣ c) (hcq : ¬ (q : ℤ) ∣ c) :
    |∑ x ∈ S, (jacobiSym (c * j x) p : ℝ) * (jacobiSym (c * j x) q : ℝ)| =
      |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)| := by
  have heq : (∑ x ∈ S,
      (jacobiSym (c * j x) p : ℝ) * (jacobiSym (c * j x) q : ℝ)) =
      (jacobiSym c p : ℝ) * (jacobiSym c q : ℝ) *
        ∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [jacobiSym.mul_left, jacobiSym.mul_left, Int.cast_mul, Int.cast_mul]
    ring
  rw [heq, abs_mul, abs_mul, abs_jacobiSym_at_prime_eq_one c p hp hcp,
    abs_jacobiSym_at_prime_eq_one c q hq hcq, one_mul, one_mul]

/-- The manuscript's literal square-factor detector, retaining the original
accepted set and using only correlations of the remaining factor. -/
theorem squareSieve_finite_detector_squareFactor
    {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset ℕ)
    (f r j : α → ℤ) (c : ℤ)
    (hfactor : ∀ x ∈ S, f x = c * (r x) ^ 2 * j x)
    (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hc : ∀ p ∈ P, ¬ (p : ℤ) ∣ c)
    (hbad : ∀ x ∈ S, f x ≠ 0 → IsSquare (f x) →
      2 * (P.filter (fun p : ℕ => (p : ℤ) ∣ f x)).card ≤ P.card) :
    ((S.filter (fun x => f x ≠ 0 ∧ IsSquare (f x))).card : ℝ) ≤
      4 * (S.card : ℝ) / (P.card : ℝ) + 4 / (P.card : ℝ) ^ 2 *
        ∑ p ∈ P, ∑ q ∈ P.erase p,
          |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)| := by
  have hsquare (x : α) (hx : x ∈ S) (hn : f x ≠ 0) (hs : IsSquare (f x)) :
      IsSquare (c * j x) := by
    have hr : r x ≠ 0 := by
      intro hz
      apply hn
      simp [hfactor x hx, hz]
    apply isSquare_of_isSquare_mul_sq_int (c * j x) (r x) hr
    convert hs using 1
    rw [hfactor x hx]
    ring
  have h := squareSieve_finite_detector_subset S
    (S.filter (fun x => f x ≠ 0 ∧ IsSquare (f x))) P (fun x => c * j x)
    (Finset.filter_subset ..) hP hprime
    (fun x hx => hsquare x (Finset.mem_filter.mp hx).1
      (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hx).2.2) (by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hx, hn, hs⟩
      have hsub : P.filter (fun p : ℕ => (p : ℤ) ∣ c * j x) ⊆
          P.filter (fun p : ℕ => (p : ℤ) ∣ f x) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hd⟩
        apply Finset.mem_filter.mpr ⟨hp, ?_⟩
        rw [hfactor x hx]
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_left hd ((r x) ^ 2)
      exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans (hbad x hx hn hs))
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact (abs_sum_jacobiSym_const_mul_correlation S j c p q (hprime p hp)
    (hprime q (Finset.mem_of_mem_erase hq)) (hc p hp)
    (hc q (Finset.mem_of_mem_erase hq))).symm

end PellPaper
