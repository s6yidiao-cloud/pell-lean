import Pell.OddJacobiReciprocalPolynomial
import Pell.JacobiPrefixCancellation
import Pell.SquareProductReciprocalDiagonal
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A finite second moment of actual odd Jacobi reciprocal polynomials

Square products use the uniform reciprocal diagonal bound. Every other
product is a positive odd nonsquare modulus, so the proved imprimitive-capable
character estimate applies. The sum over discriminant numerators is enlarged
to all positive integers at most `X`; no fundamentality or squarefreeness is
assumed in this finite estimate.
-/

open scoped BigOperators

namespace PellPaper

private theorem jacobi_real_le_one (d q : ℕ) :
    (jacobiSym (d : ℤ) q : ℝ) ≤ 1 := by
  rcases jacobiSym.trichotomy (d : ℤ) q with h | h | h <;> rw [h] <;> norm_num

private theorem sum_jacobi_real_le_cutoff (q X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, (jacobiSym (d : ℤ) q : ℝ)) ≤ X := by
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 X, (1 : ℝ) :=
      Finset.sum_le_sum (fun d _ ↦ jacobi_real_le_one d q)
    _ = X := by simp

/-- The literal odd polynomial moment, with absolute diagonal constant eight
and a uniform elementary off-diagonal error. -/
theorem sum_oddJacobiReciprocalPolynomial_sq_le
    (N X : ℕ) (hN : 0 < N) :
    (∑ d ∈ Finset.Icc 1 X, (oddJacobiReciprocalPolynomial d N) ^ 2) ≤
      8 * (X : ℝ) +
        2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 2 := by
  classical
  let I := Finset.Icc 1 N
  let O := I.filter Odd
  let S := O.product O
  let w : ℕ × ℕ → ℝ := fun p ↦ 1 / ((p.1 : ℝ) * p.2)
  let C : ℕ × ℕ → ℝ := fun p ↦
    ∑ d ∈ Finset.Icc 1 X, (jacobiSym (d : ℤ) (p.1 * p.2) : ℝ)
  let B : ℝ := 2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw (p : ℕ × ℕ) : 0 ≤ w p := by dsimp [w]; positivity
  have hmem {p : ℕ × ℕ} (hp : p ∈ S) :
      (0 < p.1 ∧ p.1 ≤ N ∧ Odd p.1) ∧
        (0 < p.2 ∧ p.2 ≤ N ∧ Odd p.2) := by
    simpa only [S, O, I, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter,
      Finset.mem_Icc, Nat.succ_le_iff, and_assoc] using hp
  have hexpand (d : ℕ) :
      (oddJacobiReciprocalPolynomial d N) ^ 2 =
        ∑ p ∈ S, w p * (jacobiSym (d : ℤ) (p.1 * p.2) : ℝ) := by
    rw [oddJacobiReciprocalPolynomial, pow_two, Finset.sum_mul_sum]
    rw [show S = O.product O from rfl, Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    have hn0 : n ≠ 0 := (show 0 < n from
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1).ne'
    have hm0 : m ≠ 0 := (show 0 < m from
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1).ne'
    dsimp [w]
    rw [jacobiSym.mul_right' _ hn0 hm0, Int.cast_mul]
    ring
  have hmoment :
      (∑ d ∈ Finset.Icc 1 X, (oddJacobiReciprocalPolynomial d N) ^ 2) =
        ∑ p ∈ S, w p * C p := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    simp only [C, Finset.mul_sum]
  have hpoint {p : ℕ × ℕ} (hp : p ∈ S) :
      C p ≤ (if IsSquare (p.1 * p.2) then (X : ℝ) else 0) + B := by
    by_cases hs : IsSquare (p.1 * p.2)
    · rw [if_pos hs]
      exact (sum_jacobi_real_le_cutoff _ X).trans (le_add_of_nonneg_right hB)
    · rw [if_neg hs, zero_add]
      obtain ⟨⟨hn, hnN, hno⟩, ⟨hm, hmN, hmo⟩⟩ := hmem hp
      exact (le_abs_self (C p)).trans
        (abs_sum_jacobiSym_mul_le_truncation p.1 p.2 N X hn hm hnN hmN
          (hno.mul hmo) hs)
  have hdiag : (∑ p ∈ S.filter (fun p ↦ IsSquare (p.1 * p.2)), w p) ≤ 8 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ ↦ hw p)).trans
      (sum_reciprocal_mul_filter_isSquare_le_eight N)
    intro p hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hp1).1, (Finset.mem_filter.mp hp2).1⟩, hs⟩
  have hweight : (∑ p ∈ S, w p) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
    have hO : (∑ n ∈ O, (n : ℝ)⁻¹) ≤ 1 + Real.log (N : ℝ) := by
      calc
        _ ≤ ∑ n ∈ I, (n : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ ↦ by positivity)
        _ = (harmonic N : ℝ) := by
          simp only [I, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        _ ≤ _ := harmonic_le_one_add_log N
    calc
      _ = (∑ n ∈ O, (n : ℝ)⁻¹) ^ 2 := by
        simp only [S, w, Finset.product_eq_sprod, Finset.sum_product, one_div, mul_inv, pow_two,
          Finset.sum_mul_sum]
      _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ by positivity)) hO 2
  calc
    _ = ∑ p ∈ S, w p * C p := hmoment
    _ ≤ ∑ p ∈ S, w p *
        ((if IsSquare (p.1 * p.2) then (X : ℝ) else 0) + B) :=
      Finset.sum_le_sum (fun p hp ↦ mul_le_mul_of_nonneg_left (hpoint hp) (hw p))
    _ = (X : ℝ) * (∑ p ∈ S.filter (fun p ↦ IsSquare (p.1 * p.2)), w p) +
        B * (∑ p ∈ S, w p) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter]
      congr 1
      · apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> ring
      · apply Finset.sum_congr rfl
        intro p _
        ring
    _ ≤ (X : ℝ) * 8 + B * (1 + Real.log (N : ℝ)) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
        (mul_le_mul_of_nonneg_left hweight hB)
    _ = _ := by dsimp [B]; ring

end PellPaper
