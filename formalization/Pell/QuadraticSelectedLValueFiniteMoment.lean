import Pell.JacobiPolynomialSecondMoment
import Pell.QuadraticSelectedLValueTruncation
import Pell.ClassAverageSecondMoment

/-!
# Finite second moments of the actual selected L-values

The exact positive-fundamental family keeps its strict cutoff `D < M`.
The polynomial-square contribution is enlarged to all integers in `[1,M]`;
the truncation errors use the actual family's proved cardinality bound.
No second-moment or truncation input is assumed. This file makes only finite
estimates, including a cubic-cutoff specialization, not an eventual assertion.
-/

namespace PellPaper

open scoped BigOperators

/-- A finite second-moment estimate for the actual selected family, with
independent positive natural numerator and truncation cutoffs. -/
theorem sum_selectedKroneckerLValue_sq_le_finite_moment
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    (∑ D ∈ fundamentalDiscriminantsBelow (M : ℝ),
      (selectedKroneckerLValue D) ^ 2) ≤
      64 * (M : ℝ) +
        16 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 2 +
        256 * (M : ℝ) ^ 2 * (1 + Real.log (2 * (M : ℝ))) ^ 2 / (N : ℝ) ^ 2 := by
  let s := fundamentalDiscriminantsBelow (M : ℝ)
  let E : ℝ :=
    256 * (M : ℝ) * (1 + Real.log (2 * (M : ℝ))) ^ 2 / (N : ℝ) ^ 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hpoint (D : ℕ) (hD : D ∈ s) :
      (selectedKroneckerLValue D) ^ 2 ≤
        8 * (oddJacobiReciprocalPolynomial D N) ^ 2 + E := by
    obtain ⟨hfund, hDM⟩ := mem_fundamentalDiscriminantsBelow.mp hD
    have hDpos : 0 < (D : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hfund.1)
    have hlogD : 0 ≤ 1 + Real.log (2 * (D : ℝ)) := by
      have hDone : (1 : ℝ) ≤ D := by exact_mod_cast (Nat.le_of_lt hfund.1)
      have hlog : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by linarith)
      linarith
    have hlog : 1 + Real.log (2 * (D : ℝ)) ≤
        1 + Real.log (2 * (M : ℝ)) := by
      exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith))
    have herror :
        256 * (D : ℝ) * (1 + Real.log (2 * (D : ℝ))) ^ 2 / (N : ℝ) ^ 2 ≤ E := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg (N : ℝ))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hDM.le (by norm_num))
        (pow_le_pow_left₀ hlogD hlog 2) (sq_nonneg _) (by positivity)
    exact (selectedKroneckerLValue_sq_le_oddJacobiReciprocalPolynomial D N hfund hN).trans
      (add_le_add le_rfl herror)
  have hsubset : s ⊆ Finset.Icc 1 M := by
    intro D hD
    obtain ⟨hfund, hDM⟩ := mem_fundamentalDiscriminantsBelow.mp hD
    exact Finset.mem_Icc.mpr ⟨by have := hfund.1; omega, by exact_mod_cast hDM.le⟩
  have hcard : (s.card : ℝ) ≤ M :=
    fundamentalDiscriminantsBelow_card_le (le_of_lt (by exact_mod_cast hM : 0 < (M : ℝ)))
  have hpoly :
      (∑ D ∈ s, (oddJacobiReciprocalPolynomial D N) ^ 2) ≤
        8 * (M : ℝ) + 2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun D _ _ ↦ sq_nonneg _)).trans
      (sum_oddJacobiReciprocalPolynomial_sq_le N M hN)
  calc
    (∑ D ∈ s, (selectedKroneckerLValue D) ^ 2) ≤
        ∑ D ∈ s, (8 * (oddJacobiReciprocalPolynomial D N) ^ 2 + E) :=
      Finset.sum_le_sum hpoint
    _ = 8 * (∑ D ∈ s, (oddJacobiReciprocalPolynomial D N) ^ 2) + (s.card : ℝ) * E := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 8 *
          (8 * (M : ℝ) + 2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)) *
            (1 + Real.log (N : ℝ)) ^ 2) + (M : ℝ) * E :=
      add_le_add (mul_le_mul_of_nonneg_left hpoly (by norm_num))
        (mul_le_mul_of_nonneg_right hcard hE)
    _ = 64 * (M : ℝ) +
        16 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 2 +
        256 * (M : ℝ) ^ 2 * (1 + Real.log (2 * (M : ℝ))) ^ 2 / (N : ℝ) ^ 2 := by
      dsimp only [E]
      ring

/-- At numerator cutoff `Y³` and truncation cutoff `Y²`, both finite errors
are `Y²` times explicit polynomials in `log Y`. -/
theorem sum_selectedKroneckerLValue_sq_le_cubic_moment
    (Y : ℕ) (hY : 0 < Y) :
    (∑ D ∈ fundamentalDiscriminantsBelow ((Y : ℝ) ^ 3),
      (selectedKroneckerLValue D) ^ 2) ≤
      64 * (Y : ℝ) ^ 3 +
        16 * (Y : ℝ) ^ 2 * (1 + 4 * Real.log (Y : ℝ)) *
          (1 + 2 * Real.log (Y : ℝ)) ^ 2 +
        256 * (Y : ℝ) ^ 2 * (1 + Real.log 2 + 3 * Real.log (Y : ℝ)) ^ 2 := by
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hlog : Real.log (2 * (Y : ℝ) ^ 3) =
      Real.log 2 + 3 * Real.log (Y : ℝ) := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hYpos.ne'), Real.log_pow]
    norm_num
  have h := sum_selectedKroneckerLValue_sq_le_finite_moment
    (Y ^ 3) (Y ^ 2) (pow_pos hY 3) (pow_pos hY 2)
  calc
    (∑ D ∈ fundamentalDiscriminantsBelow ((Y : ℝ) ^ 3),
        (selectedKroneckerLValue D) ^ 2) ≤
        64 * (Y : ℝ) ^ 3 +
          16 * (Y : ℝ) ^ 2 * (1 + 2 * Real.log ((Y : ℝ) ^ 2)) *
            (1 + Real.log ((Y : ℝ) ^ 2)) ^ 2 +
          256 * ((Y : ℝ) ^ 3) ^ 2 * (1 + Real.log (2 * (Y : ℝ) ^ 3)) ^ 2 /
            ((Y : ℝ) ^ 2) ^ 2 := by
      simpa only [Nat.cast_pow] using h
    _ = 64 * (Y : ℝ) ^ 3 +
        16 * (Y : ℝ) ^ 2 * (1 + 4 * Real.log (Y : ℝ)) *
          (1 + 2 * Real.log (Y : ℝ)) ^ 2 +
        256 * (Y : ℝ) ^ 2 * (1 + Real.log 2 + 3 * Real.log (Y : ℝ)) ^ 2 := by
      rw [hlog]
      simp only [Real.log_pow, Nat.cast_ofNat]
      field_simp
      ring

end PellPaper
