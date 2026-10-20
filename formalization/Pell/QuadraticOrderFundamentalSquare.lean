import Pell.QuadraticOrderDiscriminants
import Mathlib.Data.Rat.Lemmas

/-!
# Fundamental discriminants and square conductors

Each positive quadratic-order discriminant has a positive square conductor
over a positive fundamental discriminant. Existence is enough for the
nonnegative summation route; no choice of a representation is assumed.
-/

namespace PellPaper

private theorem isSquare_nat_of_mul_sq {d f : ℕ} (hf : 0 < f)
    (h : IsSquare (d * f ^ 2)) : IsSquare d := by
  apply Rat.isSquare_natCast_iff.mp
  have hq : IsSquare ((d : ℚ) * (f : ℚ) ^ 2) := by
    exact_mod_cast h
  have hfq : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  simpa only [mul_div_cancel_right₀ _ (pow_ne_zero 2 hfq)] using
    hq.div (IsSquare.sq (f : ℚ))

/-- Positive square conductors preserve the arithmetic order-discriminant
predicate, including at even conductors. -/
theorem positiveQuadraticOrderDiscriminant_mul_sq
    {D f : ℕ} (hD : PositiveQuadraticOrderDiscriminant D) (hf : 0 < f) :
    PositiveQuadraticOrderDiscriminant (D * f ^ 2) := by
  refine ⟨Nat.mul_pos hD.1 (pow_pos hf 2),
    fun h => hD.2.1 (isSquare_nat_of_mul_sq hf h), ?_⟩
  rcases hD.2.2 with hmod | hmod
  · left
    simp [Nat.mul_mod, hmod]
  · have hfmod : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : f % 4 <;> simp [Nat.mul_mod, Nat.pow_mod, hmod, h]

/-- Every discriminant in the broader theorem has an actual positive
fundamental discriminant and positive integer square conductor. -/
theorem exists_positiveFundamental_mul_sq_of_positiveQuadraticOrderDiscriminant
    {D : ℕ} (hD : PositiveQuadraticOrderDiscriminant D) :
    ∃ D₀ f : ℕ, PositiveFundamentalDiscriminant D₀ ∧ 0 < f ∧ D = D₀ * f ^ 2 := by
  obtain ⟨d, s, hd, hs, hDs, hsq⟩ := Nat.sq_mul_squarefree_of_pos hD.1
  have hd1 : 1 < d := by
    by_contra hn
    have hdEq : d = 1 := by omega
    apply hD.2.1
    refine ⟨s, ?_⟩
    simpa only [hdEq, mul_one, pow_two] using hDs.symm
  by_cases hmod : d % 4 = 1
  · exact ⟨d, s, ⟨hd1, Or.inl ⟨hsq, hmod⟩⟩, hs,
      hDs.symm.trans (mul_comm _ _)⟩
  · have hmod0 : d % 4 ≠ 0 := by
      intro hz
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two)
        (by simpa using Nat.dvd_of_mod_eq_zero hz)
    have hmod4 : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hdmod : d % 4 = 2 ∨ d % 4 = 3 := by omega
    have hsEven : 2 ∣ s := by
      have hsm : s % 4 < 4 := Nat.mod_lt s (by norm_num)
      have hgood := hD.2.2
      rw [← hDs] at hgood
      rcases hdmod with hm | hm <;>
        interval_cases h : s % 4 <;>
        simp [Nat.mul_mod, Nat.pow_mod, hm, h] at hgood
      all_goals omega
    obtain ⟨f, hf⟩ := hsEven
    refine ⟨4 * d, f, ⟨by omega, Or.inr ⟨d, rfl, hsq, hdmod⟩⟩,
      by omega, ?_⟩
    rw [← hDs, hf]
    ring

/-- Exact arithmetic characterization of the all-order family. Uniqueness
is not needed for the covering and nonnegative summation applications. -/
theorem positiveQuadraticOrderDiscriminant_iff_exists_fundamental_mul_sq {D : ℕ} :
    PositiveQuadraticOrderDiscriminant D ↔
      ∃ D₀ f : ℕ, PositiveFundamentalDiscriminant D₀ ∧ 0 < f ∧ D = D₀ * f ^ 2 := by
  constructor
  · exact exists_positiveFundamental_mul_sq_of_positiveQuadraticOrderDiscriminant
  · rintro ⟨D₀, f, hD₀, hf, rfl⟩
    exact positiveQuadraticOrderDiscriminant_mul_sq
      (positiveQuadraticOrderDiscriminant_of_positiveFundamental hD₀) hf

end PellPaper
