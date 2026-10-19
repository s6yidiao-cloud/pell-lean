import Pell.FriedlanderIwaniecSixthRoot
import Pell.QuadraticKroneckerCharacterScratch

/-!
# Quadratic-reciprocity transpose for the FI bilinear estimate

The one-sided sixth-root argument applies when the Jacobi numerator cutoff is
at least the denominator cutoff.  In the opposite range, transposition is
not a literal symmetry: quadratic reciprocity contributes `chi_4` on the
numerator when the old numerator is `3 mod 4`.  This module performs the
exact two-branch decomposition and obtains the real global specialization of
Friedlander--Iwaniec's equation (17).
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

def friedlanderIwaniecModFourOnePart
    (alpha : ℕ → ℝ) (m : ℕ) : ℝ :=
  if Odd m ∧ m % 4 = 1 then alpha m else 0

def friedlanderIwaniecModFourThreePart
    (alpha : ℕ → ℝ) (m : ℕ) : ℝ :=
  if Odd m ∧ m % 4 = 3 then alpha m else 0

def friedlanderIwaniecChiFourTwist
    (beta : ℕ → ℝ) (n : ℕ) : ℝ :=
  beta n * (ZMod.χ₄ (n : ZMod 4) : ℝ)

private theorem abs_chiFour_real_le_one (n : ℕ) :
    |(ZMod.χ₄ (n : ZMod 4) : ℝ)| ≤ 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

theorem abs_friedlanderIwaniecModFourOnePart_le_one
    (alpha : ℕ → ℝ) (halpha : ∀ m : ℕ, |alpha m| ≤ 1) (m : ℕ) :
    |friedlanderIwaniecModFourOnePart alpha m| ≤ 1 := by
  unfold friedlanderIwaniecModFourOnePart
  split_ifs
  · exact halpha m
  · norm_num

theorem abs_friedlanderIwaniecModFourThreePart_le_one
    (alpha : ℕ → ℝ) (halpha : ∀ m : ℕ, |alpha m| ≤ 1) (m : ℕ) :
    |friedlanderIwaniecModFourThreePart alpha m| ≤ 1 := by
  unfold friedlanderIwaniecModFourThreePart
  split_ifs
  · exact halpha m
  · norm_num

theorem friedlanderIwaniecModFourOnePart_eq_zero_of_even
    (alpha : ℕ → ℝ) (m : ℕ) (hm : Even m) :
    friedlanderIwaniecModFourOnePart alpha m = 0 := by
  unfold friedlanderIwaniecModFourOnePart
  rw [if_neg]
  exact fun h ↦ (Nat.not_odd_iff_even.mpr hm) h.1

theorem friedlanderIwaniecModFourThreePart_eq_zero_of_even
    (alpha : ℕ → ℝ) (m : ℕ) (hm : Even m) :
    friedlanderIwaniecModFourThreePart alpha m = 0 := by
  unfold friedlanderIwaniecModFourThreePart
  rw [if_neg]
  exact fun h ↦ (Nat.not_odd_iff_even.mpr hm) h.1

theorem abs_friedlanderIwaniecChiFourTwist_le_one
    (beta : ℕ → ℝ) (hbeta : ∀ n : ℕ, |beta n| ≤ 1) (n : ℕ) :
    |friedlanderIwaniecChiFourTwist beta n| ≤ 1 := by
  unfold friedlanderIwaniecChiFourTwist
  rw [abs_mul]
  exact (mul_le_mul (hbeta n) (abs_chiFour_real_le_one n)
    (abs_nonneg _) (by norm_num)).trans (by norm_num)

private theorem friedlanderIwaniec_reciprocity_split_pointwise
    (alpha beta : ℕ → ℝ)
    (halphaEven : ∀ m : ℕ, Even m → alpha m = 0)
    (hbetaEven : ∀ n : ℕ, Even n → beta n = 0)
    (m n : ℕ) :
    alpha m * beta n * (jacobiSym (m : ℤ) n : ℝ) =
      beta n * friedlanderIwaniecModFourOnePart alpha m *
          (jacobiSym (n : ℤ) m : ℝ) +
        friedlanderIwaniecChiFourTwist beta n *
          friedlanderIwaniecModFourThreePart alpha m *
            (jacobiSym (n : ℤ) m : ℝ) := by
  by_cases hn : Odd n
  · by_cases hm : Odd m
    · rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm1 | hm3
      · have hrec := jacobiSym.quadratic_reciprocity_one_mod_four hm1 hn
        have hrecR : (jacobiSym (m : ℤ) n : ℝ) =
            (jacobiSym (n : ℤ) m : ℝ) := by exact_mod_cast hrec
        have hpartOne : friedlanderIwaniecModFourOnePart alpha m = alpha m := by
          unfold friedlanderIwaniecModFourOnePart
          rw [if_pos ⟨hm, hm1⟩]
        have hpartThree : friedlanderIwaniecModFourThreePart alpha m = 0 := by
          unfold friedlanderIwaniecModFourThreePart
          rw [if_neg]
          intro h
          omega
        rw [hrecR]
        rw [hpartOne, hpartThree]
        simp only [mul_zero, zero_mul, add_zero]
        ring
      · have hrec :=
          jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
            m n hm3 hn
        have hrecR : (jacobiSym (m : ℤ) n : ℝ) =
            (ZMod.χ₄ (n : ZMod 4) : ℝ) *
              (jacobiSym (n : ℤ) m : ℝ) := by exact_mod_cast hrec
        have hpartOne : friedlanderIwaniecModFourOnePart alpha m = 0 := by
          unfold friedlanderIwaniecModFourOnePart
          rw [if_neg]
          intro h
          omega
        have hpartThree :
            friedlanderIwaniecModFourThreePart alpha m = alpha m := by
          unfold friedlanderIwaniecModFourThreePart
          rw [if_pos ⟨hm, hm3⟩]
        rw [hrecR]
        rw [hpartOne, hpartThree]
        unfold friedlanderIwaniecChiFourTwist
        simp only [mul_zero, zero_mul, zero_add]
        ring
    · have hmEven : Even m := Nat.not_odd_iff_even.mp hm
      rw [halphaEven m hmEven,
        friedlanderIwaniecModFourOnePart_eq_zero_of_even alpha m hmEven,
        friedlanderIwaniecModFourThreePart_eq_zero_of_even alpha m hmEven]
      ring
  · have hnEven : Even n := Nat.not_odd_iff_even.mp hn
    have hbetaZero := hbetaEven n hnEven
    rw [hbetaZero]
    unfold friedlanderIwaniecChiFourTwist
    rw [hbetaZero]
    ring

/-- Exact two-branch transpose identity. -/
theorem friedlanderIwaniecJacobiBilinear_eq_reciprocity_transpose
    (alpha beta : ℕ → ℝ) (M N : ℕ)
    (halphaEven : ∀ m : ℕ, Even m → alpha m = 0)
    (hbetaEven : ∀ n : ℕ, Even n → beta n = 0) :
    friedlanderIwaniecJacobiBilinear alpha beta M N =
      friedlanderIwaniecJacobiBilinear beta
          (friedlanderIwaniecModFourOnePart alpha) N M +
      friedlanderIwaniecJacobiBilinear
          (friedlanderIwaniecChiFourTwist beta)
          (friedlanderIwaniecModFourThreePart alpha) N M := by
  conv_lhs =>
    rw [friedlanderIwaniecJacobiBilinear_eq_sum_modulus]
  unfold friedlanderIwaniecJacobiBilinear
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    friedlanderIwaniec_reciprocity_split_pointwise
      alpha beta halphaEven hbetaEven m n

theorem friedlanderIwaniecBilinearScale_comm (M N : ℕ) :
    friedlanderIwaniecBilinearScale M N =
      friedlanderIwaniecBilinearScale N M := by
  unfold friedlanderIwaniecBilinearScale
  congr 1
  · ring
  · congr 2
    ring

theorem friedlanderIwaniecBilinearScale_nonneg (M N : ℕ) :
    0 ≤ friedlanderIwaniecBilinearScale M N := by
  by_cases hM0 : M = 0
  · subst M
    simp [friedlanderIwaniecBilinearScale]
  by_cases hN0 : N = 0
  · subst N
    simp [friedlanderIwaniecBilinearScale]
  have hMone : (1 : ℝ) ≤ M := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM0)
  have hNone : (1 : ℝ) ≤ N := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN0)
  have hlog : 0 ≤ Real.log (3 * (M : ℝ) * (N : ℝ)) := by
    apply Real.log_nonneg
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ M by positivity)
      (show (0 : ℝ) ≤ N by positivity)]
  unfold friedlanderIwaniecBilinearScale
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (by positivity)
        (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (by positivity)))
    (Real.rpow_nonneg hlog _)

/-- Global real FI estimate, with an explicit absolute constant four. -/
theorem abs_friedlanderIwaniecJacobiBilinear_le_four_mul_scale
    (alpha beta : ℕ → ℝ) (M N : ℕ)
    (hM : 2 ≤ M) (hN : 2 ≤ N)
    (halphaEven : ∀ m : ℕ, Even m → alpha m = 0)
    (hbetaEven : ∀ n : ℕ, Even n → beta n = 0)
    (halpha : ∀ m : ℕ, |alpha m| ≤ 1)
    (hbeta : ∀ n : ℕ, |beta n| ≤ 1) :
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ≤
      4 * friedlanderIwaniecBilinearScale M N := by
  by_cases hNM : N ≤ M
  · exact (abs_friedlanderIwaniecJacobiBilinear_le_two_mul_scale_of_le
      alpha beta M N hN hNM (fun m _ ↦ halpha m) hbetaEven hbeta).trans
        (by
          have hs := friedlanderIwaniecBilinearScale_nonneg M N
          linarith)
  · have hMN : M ≤ N := by omega
    rw [friedlanderIwaniecJacobiBilinear_eq_reciprocity_transpose
      alpha beta M N halphaEven hbetaEven]
    calc
      |friedlanderIwaniecJacobiBilinear beta
            (friedlanderIwaniecModFourOnePart alpha) N M +
          friedlanderIwaniecJacobiBilinear
            (friedlanderIwaniecChiFourTwist beta)
            (friedlanderIwaniecModFourThreePart alpha) N M| ≤
          |friedlanderIwaniecJacobiBilinear beta
            (friedlanderIwaniecModFourOnePart alpha) N M| +
          |friedlanderIwaniecJacobiBilinear
            (friedlanderIwaniecChiFourTwist beta)
            (friedlanderIwaniecModFourThreePart alpha) N M| := abs_add_le _ _
      _ ≤ 2 * friedlanderIwaniecBilinearScale N M +
          2 * friedlanderIwaniecBilinearScale N M := by
        exact add_le_add
          (abs_friedlanderIwaniecJacobiBilinear_le_two_mul_scale_of_le
            beta (friedlanderIwaniecModFourOnePart alpha) N M hM hMN
            (fun n _ ↦ hbeta n)
            (friedlanderIwaniecModFourOnePart_eq_zero_of_even alpha)
            (abs_friedlanderIwaniecModFourOnePart_le_one alpha halpha))
          (abs_friedlanderIwaniecJacobiBilinear_le_two_mul_scale_of_le
            (friedlanderIwaniecChiFourTwist beta)
            (friedlanderIwaniecModFourThreePart alpha) N M hM hMN
            (fun n _ ↦ abs_friedlanderIwaniecChiFourTwist_le_one beta hbeta n)
            (friedlanderIwaniecModFourThreePart_eq_zero_of_even alpha)
            (abs_friedlanderIwaniecModFourThreePart_le_one alpha halpha))
      _ = 4 * friedlanderIwaniecBilinearScale M N := by
        rw [← friedlanderIwaniecBilinearScale_comm M N]
        ring

end

end PellPaper
