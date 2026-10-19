import Pell.JacobiPrefixCancellation
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Hölder reduction in the Friedlander--Iwaniec bilinear estimate

This module isolates the first inequality in Section 9, p. 111, of
Friedlander--Iwaniec, *Ternary quadratic forms with rational zeros* (JTNB 22
(2010), DOI 10.5802/jtnb.706).  It is entirely finite and elementary: after
commuting the two sums, the coefficient bound and the cubic power-mean
inequality give the printed factor `N^2`.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The source-oriented bilinear Jacobi sum `B(M,N)` in
Friedlander--Iwaniec's equation (17). -/
def friedlanderIwaniecJacobiBilinear
    (alpha beta : ℕ → ℝ) (M N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, alpha m *
    ∑ n ∈ Finset.Icc 1 N,
      beta n * (jacobiSym (m : ℤ) n : ℝ)

/-- Commuting the rectangle writes `B(M,N)` as a sum over its modulus
variable, which is the orientation used for the Hölder step. -/
theorem friedlanderIwaniecJacobiBilinear_eq_sum_modulus
    (alpha beta : ℕ → ℝ) (M N : ℕ) :
    friedlanderIwaniecJacobiBilinear alpha beta M N =
      ∑ n ∈ Finset.Icc 1 N, beta n *
        ∑ m ∈ Finset.Icc 1 M,
          alpha m * (jacobiSym (m : ℤ) n : ℝ) := by
  unfold friedlanderIwaniecJacobiBilinear
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- The exact finite Hölder inequality at the start of FI Section 9.
The source assumes odd support as well, but that hypothesis is not needed
until the later character-cancellation step. -/
theorem abs_friedlanderIwaniecJacobiBilinear_pow_three_le
    (alpha beta : ℕ → ℝ) (M N : ℕ)
    (hbeta : ∀ n ∈ Finset.Icc 1 N, |beta n| ≤ 1) :
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 3 ≤
      (N : ℝ) ^ 2 *
        ∑ n ∈ Finset.Icc 1 N,
          |∑ m ∈ Finset.Icc 1 M,
            alpha m * (jacobiSym (m : ℤ) n : ℝ)| ^ 3 := by
  let A : ℕ → ℝ := fun n ↦
    ∑ m ∈ Finset.Icc 1 M,
      alpha m * (jacobiSym (m : ℤ) n : ℝ)
  have habs :
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ≤
        ∑ n ∈ Finset.Icc 1 N, |A n| := by
    rw [friedlanderIwaniecJacobiBilinear_eq_sum_modulus]
    calc
      |∑ n ∈ Finset.Icc 1 N, beta n * A n| ≤
          ∑ n ∈ Finset.Icc 1 N, |beta n * A n| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, |A n| := by
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg (A n)) (hbeta n hn)
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 3
  refine hpow.trans ?_
  have hholder := pow_sum_le_card_mul_sum_pow
    (s := Finset.Icc 1 N) (f := fun n ↦ |A n|)
    (fun n _hn ↦ abs_nonneg (A n)) 2
  have hcard : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa only [Nat.reduceAdd, hcard, Nat.cast_pow, A] using hholder

/-- Source-faithful odd-supported form of the Hölder reduction.  Terms with
even modulus vanish before Hölder is applied, so the later Jacobi-character
cancellation only encounters odd moduli. -/
theorem abs_friedlanderIwaniecJacobiBilinear_pow_three_le_odd
    (alpha beta : ℕ → ℝ) (M N : ℕ)
    (hbetaEven : ∀ n : ℕ, Even n → beta n = 0)
    (hbeta : ∀ n : ℕ, |beta n| ≤ 1) :
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 3 ≤
      (N : ℝ) ^ 2 *
        ∑ n ∈ (Finset.Icc 1 N).filter Odd,
          |∑ m ∈ Finset.Icc 1 M,
            alpha m * (jacobiSym (m : ℤ) n : ℝ)| ^ 3 := by
  let I := Finset.Icc 1 N
  let O := I.filter Odd
  let A : ℕ → ℝ := fun n ↦
    ∑ m ∈ Finset.Icc 1 M,
      alpha m * (jacobiSym (m : ℤ) n : ℝ)
  have hrestrict :
      friedlanderIwaniecJacobiBilinear alpha beta M N =
        ∑ n ∈ O, beta n * A n := by
    rw [friedlanderIwaniecJacobiBilinear_eq_sum_modulus]
    change (∑ n ∈ I, beta n * A n) = ∑ n ∈ I.filter Odd, beta n * A n
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hnOdd : Odd n
    · simp [hnOdd]
    · have hnEven : Even n := Nat.not_odd_iff_even.mp hnOdd
      simp [hnOdd, hbetaEven n hnEven]
  have habs :
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ≤
        ∑ n ∈ O, |A n| := by
    rw [hrestrict]
    calc
      |∑ n ∈ O, beta n * A n| ≤
          ∑ n ∈ O, |beta n * A n| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ O, |A n| := by
        apply Finset.sum_le_sum
        intro n _hn
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg (A n)) (hbeta n)
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 3
  have hholder := pow_sum_le_card_mul_sum_pow
    (s := O) (f := fun n ↦ |A n|)
    (fun n _hn ↦ abs_nonneg (A n)) 2
  have hcardNat : O.card ≤ N := by
    calc
      O.card ≤ I.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = N := by
        dsimp only [I]
        rw [Nat.card_Icc]
        omega
  have hcard : (O.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hcardNat 2
  have hsumNonneg : 0 ≤ ∑ n ∈ O, |A n| ^ 3 := by positivity
  calc
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 3 ≤
        (∑ n ∈ O, |A n|) ^ 3 := hpow
    _ ≤ (O.card : ℝ) ^ 2 * ∑ n ∈ O, |A n| ^ 3 := by
      simpa only [Nat.reduceAdd, Nat.cast_pow] using hholder
    _ ≤ (N : ℝ) ^ 2 * ∑ n ∈ O, |A n| ^ 3 :=
      mul_le_mul_of_nonneg_right hcard hsumNonneg

end

end PellPaper
