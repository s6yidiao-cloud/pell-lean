import Pell.SquareSieveGoodPrimeAnnulus
import Mathlib.Tactic

/-!
# Quantitative aggregation of the actual square-sieve correlations

Bounding every off-diagonal correlation removes the ordered prime-pair sum.
The actual good-prime density then removes the reciprocal prime count as well.
The remaining hypothesis is an individual ambient Jacobi correlation bound.
-/

open scoped BigOperators
open Filter

namespace PellPaper

private theorem sum_offDiagonal_le_card_sq_mul
    (P : Finset ℕ) (F : ℕ → ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → F p q ≤ B) :
    (∑ p ∈ P, ∑ q ∈ P.erase p, F p q) ≤ (P.card : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ p ∈ P, ∑ _q ∈ P.erase p, B := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact hF p hp q (Finset.mem_erase.mp hq).2 (Finset.mem_erase.mp hq).1.symm
    _ ≤ ∑ _p ∈ P, ∑ _q ∈ P, B := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p P)
        (by intros; exact hB)
    _ = _ := by simp [pow_two, mul_assoc]

/-- The logarithmic square-factor detector with its complete ordered
prime-pair sum evaluated using a uniform individual correlation bound. -/
theorem squareSieve_logarithmic_squareFactor_le_of_correlation_bound
    {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset ℕ)
    (f r j : α → ℤ) (c : ℤ) (N W B : ℝ)
    (hfactor : ∀ x ∈ S, f x = c * (r x) ^ 2 * j x)
    (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hc : ∀ p ∈ P, ¬ (p : ℤ) ∣ c) (hN : 1 < N)
    (hlower : ∀ p ∈ P, N ≤ (p : ℝ))
    (hsize : ∀ x ∈ S, ((f x).natAbs : ℝ) ≤ W)
    (hbudget : 2 * Real.log W / Real.log N ≤ (P.card : ℝ))
    (hB : 0 ≤ B)
    (hcorr : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)| ≤ B) :
    ((S.filter (fun x => f x ≠ 0 ∧ IsSquare (f x))).card : ℝ) ≤
      4 * (S.card : ℝ) / (P.card : ℝ) + 4 * B := by
  have h := squareSieve_logarithmic_detector_squareFactor S P f r j c N W
    hfactor hP hprime hc hN hlower hsize hbudget
  have hR : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.card_pos.ne'
  have hsum := sum_offDiagonal_le_card_sq_mul P
    (fun p q => |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)|)
    B hB hcorr
  apply h.trans
  apply add_le_add_right
  calc
    _ ≤ 4 / (P.card : ℝ) ^ 2 * ((P.card : ℝ) ^ 2 * B) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * B := by field_simp

/-- One threshold in the natural sieve scale works for every finite family,
content, reduction certificate, value bound and nonnegative correlation
bound. The prime set and its cardinality are no longer supplied inputs. -/
theorem eventually_squareSieve_squareFactor_le_of_goodPrime_correlation_bound
    {α : Type*} [DecidableEq α] :
    ∀ᶠ N : ℕ in atTop, ∀ Delta c : ℤ, ∀ W B : ℝ, ∀ S : Finset α,
      ∀ f r j : α → ℤ,
      Delta ≠ 0 → c ∣ Delta →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      (∀ x ∈ S, f x = c * (r x) ^ 2 * j x) →
      (∀ x ∈ S, ((f x).natAbs : ℝ) ≤ W) → 0 ≤ B →
      (∀ p ∈ goodPrimeAnnulus N Delta, ∀ q ∈ goodPrimeAnnulus N Delta,
        p ≠ q → |∑ x ∈ S,
          (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)| ≤ B) →
      ((S.filter (fun x => f x ≠ 0 ∧ IsSquare (f x))).card : ℝ) ≤
        (32 / Real.log 2) * (S.card : ℝ) * Real.log (N : ℝ) / (N : ℝ) +
          4 * B := by
  filter_upwards [eventually_squareSieve_logarithmic_detector_squareFactor_goodPrimeAnnulus (α := α),
    eventually_goodPrimeAnnulus_card_lower, eventually_ge_atTop 4] with N hdet hcard hN
  intro Delta c W B S f r j hDelta hcDelta hDeltaSize hW hfactor hsize hB hcorr
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let R : ℝ := ((goodPrimeAnnulus N Delta).card : ℝ)
  let A : ℝ := (Real.log 2 / 8) * (N : ℝ) / Real.log (N : ℝ)
  have hA : 0 < A := div_pos (mul_pos (by positivity) hNp) hlog
  have hAR : A ≤ R := hcard Delta hDelta hDeltaSize
  have hR : 0 < R := hA.trans_le hAR
  have hsum := sum_offDiagonal_le_card_sq_mul (goodPrimeAnnulus N Delta)
    (fun p q => |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)|)
    B hB hcorr
  have h := hdet Delta c W S f r j hDelta hcDelta hDeltaSize hW hfactor hsize
  have hoff : 4 / R ^ 2 *
      (∑ p ∈ goodPrimeAnnulus N Delta, ∑ q ∈ (goodPrimeAnnulus N Delta).erase p,
        |∑ x ∈ S, (jacobiSym (j x) p : ℝ) * (jacobiSym (j x) q : ℝ)|) ≤ 4 * B := by
    calc
      _ ≤ 4 / R ^ 2 * (R ^ 2 * B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by field_simp
  have hdiag : 4 * (S.card : ℝ) / R ≤
      (32 / Real.log 2) * (S.card : ℝ) * Real.log (N : ℝ) / (N : ℝ) := by
    calc
      _ ≤ 4 * (S.card : ℝ) / A :=
        div_le_div_of_nonneg_left (by positivity) hA hAR
      _ = _ := by
        dsimp [A]
        field_simp
        ring
  exact h.trans (add_le_add hdiag hoff)

end PellPaper
