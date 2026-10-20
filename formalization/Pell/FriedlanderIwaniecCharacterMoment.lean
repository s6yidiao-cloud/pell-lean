import Pell.JacobiPrefixCancellation
import Pell.SquareProductPairCount

/-!
# The character second moment in Friedlander--Iwaniec's bilinear estimate

This module formalizes the square/nonsquare split after the cubic grouping in
Section 9, pp. 111--112, of Friedlander--Iwaniec, *Ternary quadratic forms
with rational zeros* (JTNB 22 (2010), DOI 10.5802/jtnb.706).

For coefficients of modulus at most one supported on the odd integers, the
square-product pairs contribute the length of the numerator interval, while
every nonsquare product is controlled by the already proved imprimitive
Pólya--Vinogradov estimate.  The elementary square-product count then gives
the explicit uniform envelope below.  This is one ingredient of the
published bilinear estimate, not a proof of that full estimate.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The odd-supported Jacobi column appearing after the cubic regrouping in
the Friedlander--Iwaniec argument. -/
def friedlanderIwaniecOddJacobiColumn
    (gamma : ℕ → ℝ) (N ell : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter Odd,
    gamma n * (jacobiSym (ell : ℤ) n : ℝ)

/-- Its finite second moment over positive numerators at most `L`. -/
def friedlanderIwaniecOddJacobiColumnSecondMoment
    (gamma : ℕ → ℝ) (N L : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 L,
    (friedlanderIwaniecOddJacobiColumn gamma N ell) ^ 2

private theorem abs_jacobiSym_real_le_one (a : ℤ) (q : ℕ) :
    |(jacobiSym a q : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a q with h | h | h <;> rw [h] <;> norm_num

private theorem abs_sum_jacobiSym_real_le_length (q L : ℕ) :
    |∑ ell ∈ Finset.Icc 1 L, (jacobiSym (ell : ℤ) q : ℝ)| ≤ L := by
  calc
    |∑ ell ∈ Finset.Icc 1 L, (jacobiSym (ell : ℤ) q : ℝ)| ≤
        ∑ ell ∈ Finset.Icc 1 L,
          |(jacobiSym (ell : ℤ) q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ell ∈ Finset.Icc 1 L, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun ell _ ↦ abs_jacobiSym_real_le_one ell q)
    _ = L := by simp

/-- Explicit square/nonsquare second-moment bound used in the proof of the
Friedlander--Iwaniec bilinear Jacobi-symbol estimate.

The first term is the square-product diagonal.  The second is the uniform
Pólya--Vinogradov contribution from all remaining ordered pairs. -/
theorem friedlanderIwaniecOddJacobiColumnSecondMoment_le
    (gamma : ℕ → ℝ) (N L : ℕ) (hN : 0 < N)
    (hgamma : ∀ n : ℕ, |gamma n| ≤ 1) :
    friedlanderIwaniecOddJacobiColumnSecondMoment gamma N L ≤
      (L : ℝ) * (N : ℝ) * (1 + Real.log (N : ℝ)) +
        2 * (N : ℝ) ^ 3 * (1 + 2 * Real.log (N : ℝ)) := by
  classical
  let I := Finset.Icc 1 N
  let O := I.filter Odd
  let S := O.product O
  let C : ℕ × ℕ → ℝ := fun p ↦
    ∑ ell ∈ Finset.Icc 1 L,
      (jacobiSym (ell : ℤ) (p.1 * p.2) : ℝ)
  let B : ℝ := 2 * (N : ℝ) * (1 + 2 * Real.log (N : ℝ))
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmem {p : ℕ × ℕ} (hp : p ∈ S) :
      (0 < p.1 ∧ p.1 ≤ N ∧ Odd p.1) ∧
        (0 < p.2 ∧ p.2 ≤ N ∧ Odd p.2) := by
    simpa only [S, O, I, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_filter, Finset.mem_Icc, Nat.succ_le_iff, and_assoc] using hp
  have hexpand (ell : ℕ) :
      (friedlanderIwaniecOddJacobiColumn gamma N ell) ^ 2 =
        ∑ p ∈ S,
          gamma p.1 * gamma p.2 *
            (jacobiSym (ell : ℤ) (p.1 * p.2) : ℝ) := by
    rw [friedlanderIwaniecOddJacobiColumn, pow_two, Finset.sum_mul_sum]
    rw [show S = O.product O from rfl, Finset.product_eq_sprod,
      Finset.sum_product]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    have hn0 : n ≠ 0 := (show 0 < n from
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1).ne'
    have hm0 : m ≠ 0 := (show 0 < m from
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1).ne'
    rw [jacobiSym.mul_right' _ hn0 hm0, Int.cast_mul]
    ring
  have hmoment :
      friedlanderIwaniecOddJacobiColumnSecondMoment gamma N L =
        ∑ p ∈ S, gamma p.1 * gamma p.2 * C p := by
    unfold friedlanderIwaniecOddJacobiColumnSecondMoment
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    simp only [C, Finset.mul_sum]
  have hcorrelation {p : ℕ × ℕ} (hp : p ∈ S) :
      |C p| ≤
        (if IsSquare (p.1 * p.2) then (L : ℝ) else 0) + B := by
    by_cases hs : IsSquare (p.1 * p.2)
    · rw [if_pos hs]
      exact (abs_sum_jacobiSym_real_le_length (p.1 * p.2) L).trans
        (le_add_of_nonneg_right hB)
    · rw [if_neg hs, zero_add]
      obtain ⟨⟨hn, hnN, hno⟩, ⟨hm, hmN, hmo⟩⟩ := hmem hp
      exact abs_sum_jacobiSym_mul_le_truncation p.1 p.2 N L
        hn hm hnN hmN (hno.mul hmo) hs
  have hpoint {p : ℕ × ℕ} (hp : p ∈ S) :
      gamma p.1 * gamma p.2 * C p ≤
        (if IsSquare (p.1 * p.2) then (L : ℝ) else 0) + B := by
    calc
      gamma p.1 * gamma p.2 * C p ≤
          |gamma p.1 * gamma p.2 * C p| := le_abs_self _
      _ = |gamma p.1| * |gamma p.2| * |C p| := by
        simp only [abs_mul]
      _ ≤ 1 * 1 * |C p| := by
        gcongr
        · exact hgamma p.1
        · exact hgamma p.2
      _ = |C p| := by ring
      _ ≤ _ := hcorrelation hp
  have hdiagNat :
      (S.filter (fun p ↦ IsSquare (p.1 * p.2))).card ≤
        (squareProductPairsUpTo N).card := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hpS, hpsq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpS
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hp1).1, (Finset.mem_filter.mp hp2).1⟩, hpsq⟩
  have hdiag :
      (((S.filter (fun p ↦ IsSquare (p.1 * p.2))).card : ℕ) : ℝ) ≤
        (N : ℝ) * (1 + Real.log (N : ℝ)) := by
    exact (by exact_mod_cast hdiagNat :
      (((S.filter (fun p ↦ IsSquare (p.1 * p.2))).card : ℕ) : ℝ) ≤
        ((squareProductPairsUpTo N).card : ℝ)).trans
          (card_squareProductPairsUpTo_cast_le N)
  have hScardNat : S.card ≤ N ^ 2 := by
    calc
      S.card = O.card * O.card := by simp [S]
      _ ≤ I.card * I.card := Nat.mul_le_mul
        (Finset.card_le_card (Finset.filter_subset _ _))
        (Finset.card_le_card (Finset.filter_subset _ _))
      _ = N ^ 2 := by simp [I, pow_two]
  have hScard : (S.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hScardNat
  calc
    friedlanderIwaniecOddJacobiColumnSecondMoment gamma N L =
        ∑ p ∈ S, gamma p.1 * gamma p.2 * C p := hmoment
    _ ≤ ∑ p ∈ S,
        ((if IsSquare (p.1 * p.2) then (L : ℝ) else 0) + B) :=
      Finset.sum_le_sum (fun p hp ↦ hpoint hp)
    _ = (L : ℝ) *
          ((S.filter (fun p ↦ IsSquare (p.1 * p.2))).card : ℝ) +
        B * (S.card : ℝ) := by
      simp only [Finset.sum_add_distrib]
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ (L : ℝ) * ((N : ℝ) * (1 + Real.log (N : ℝ))) +
        B * (N : ℝ) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg L))
        (mul_le_mul_of_nonneg_left hScard hB)
    _ = (L : ℝ) * (N : ℝ) * (1 + Real.log (N : ℝ)) +
        2 * (N : ℝ) ^ 3 * (1 + 2 * Real.log (N : ℝ)) := by
      dsimp [B]
      ring

/-- The coarser form printed at the end of Friedlander--Iwaniec's proof:
after taking a numerator interval of length `M^3`, the nonsquare contribution
may be absorbed into `6 * N^4`.  The source uses Vinogradov notation and does
not record this harmless explicit constant. -/
theorem friedlanderIwaniecOddJacobiColumnSecondMoment_cube_le
    (gamma : ℕ → ℝ) (M N : ℕ) (hN : 0 < N)
    (hgamma : ∀ n : ℕ, |gamma n| ≤ 1) :
    friedlanderIwaniecOddJacobiColumnSecondMoment gamma N (M ^ 3) ≤
      (M : ℝ) ^ 3 * (N : ℝ) * (1 + Real.log (N : ℝ)) +
        6 * (N : ℝ) ^ 4 := by
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < N by exact_mod_cast hN)
  have hfactor : 1 + 2 * Real.log (N : ℝ) ≤ 3 * (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hcoef : 0 ≤ 2 * (N : ℝ) ^ 3 := by positivity
  calc
    friedlanderIwaniecOddJacobiColumnSecondMoment gamma N (M ^ 3) ≤
        ((M ^ 3 : ℕ) : ℝ) * (N : ℝ) *
            (1 + Real.log (N : ℝ)) +
          2 * (N : ℝ) ^ 3 * (1 + 2 * Real.log (N : ℝ)) :=
      friedlanderIwaniecOddJacobiColumnSecondMoment_le gamma N (M ^ 3)
        hN hgamma
    _ ≤ ((M ^ 3 : ℕ) : ℝ) * (N : ℝ) *
            (1 + Real.log (N : ℝ)) +
          2 * (N : ℝ) ^ 3 * (3 * (N : ℝ)) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hfactor hcoef)
    _ = (M : ℝ) ^ 3 * (N : ℝ) *
          (1 + Real.log (N : ℝ)) + 6 * (N : ℝ) ^ 4 := by
      push_cast
      ring

end

end PellPaper
