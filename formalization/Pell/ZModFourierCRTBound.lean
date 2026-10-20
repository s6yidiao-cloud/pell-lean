import Pell.ZModFourierCRTProduct

/-!
# Fourier bounds for products transported by the Chinese remainder theorem

Local nonzero-frequency bounds, together with vanishing at the local zero
frequencies, multiply under the literal CRT Fourier factorization.  The
result feeds directly into the canonical shifted-rectangle completion
estimate.  No polynomial or character-sum estimate is assumed here beyond
the two supplied local coefficient bounds.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- Nonzero double Fourier coefficients of a CRT product are bounded by the
product of the two local coefficient constants.  If either local frequency
pair is zero, its Fourier factor vanishes exactly. -/
theorem norm_zmodFourier2_crtProduct_le_of_local_bounds
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n)
    (f : ZMod m → ZMod m → ℂ) (g : ZMod n → ZMod n → ℂ)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfzero : zmodFourier2 f 0 0 = 0)
    (hgzero : zmodFourier2 g 0 0 = 0)
    (hfbound : ∀ k l : ZMod m, (k, l) ≠ (0, 0) →
      ‖zmodFourier2 f k l‖ ≤ C₁ * (m : ℝ))
    (hgbound : ∀ k l : ZMod n, (k, l) ≠ (0, 0) →
      ‖zmodFourier2 g k l‖ ≤ C₂ * (n : ℝ))
    (k l : ZMod (m * n)) (_hkl : (k, l) ≠ (0, 0)) :
    ‖zmodFourier2 (zmodCRTProduct h f g) k l‖ ≤
      (C₁ * C₂) * ((m * n : ℕ) : ℝ) := by
  have hfbound_all (k l : ZMod m) :
      ‖zmodFourier2 f k l‖ ≤ C₁ * (m : ℝ) := by
    by_cases hkl : (k, l) = (0, 0)
    · have hk : k = 0 := congrArg Prod.fst hkl
      have hl : l = 0 := congrArg Prod.snd hkl
      subst k
      subst l
      rw [hfzero, norm_zero]
      exact mul_nonneg hC₁ (Nat.cast_nonneg m)
    · exact hfbound k l hkl
  have hgbound_all (k l : ZMod n) :
      ‖zmodFourier2 g k l‖ ≤ C₂ * (n : ℝ) := by
    by_cases hkl : (k, l) = (0, 0)
    · have hk : k = 0 := congrArg Prod.fst hkl
      have hl : l = 0 := congrArg Prod.snd hkl
      subst k
      subst l
      rw [hgzero, norm_zero]
      exact mul_nonneg hC₂ (Nat.cast_nonneg n)
    · exact hgbound k l hkl
  rw [zmodFourier2_crtProduct, norm_mul]
  calc
    ‖zmodFourier2 f (zmodCRTFirstFrequency h k)
          (zmodCRTFirstFrequency h l)‖ *
        ‖zmodFourier2 g (zmodCRTSecondFrequency h k)
          (zmodCRTSecondFrequency h l)‖ ≤
      (C₁ * (m : ℝ)) * (C₂ * (n : ℝ)) :=
        mul_le_mul
          (hfbound_all _ _) (hgbound_all _ _)
          (norm_nonneg _) (mul_nonneg hC₁ (Nat.cast_nonneg m))
    _ = (C₁ * C₂) * ((m * n : ℕ) : ℝ) := by
      push_cast
      ring

/-- The local CRT coefficient bounds imply the literal shifted-rectangle
completion bound at the product modulus.  Modulus one and empty windows are
included. -/
theorem norm_sum_box_zmodCRTProduct_le_of_local_fourier2_bounds
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n)
    (f : ZMod m → ZMod m → ℂ) (g : ZMod n → ZMod n → ℂ)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfzero : zmodFourier2 f 0 0 = 0)
    (hgzero : zmodFourier2 g 0 0 = 0)
    (hfbound : ∀ k l : ZMod m, (k, l) ≠ (0, 0) →
      ‖zmodFourier2 f k l‖ ≤ C₁ * (m : ℝ))
    (hgbound : ∀ k l : ZMod n, (k, l) ≠ (0, 0) →
      ‖zmodFourier2 g k l‖ ≤ C₂ * (n : ℝ))
    (a b : ZMod (m * n)) (L₁ L₂ : ℕ) :
    ‖∑ i ∈ Finset.range L₁, ∑ j ∈ Finset.range L₂,
        zmodCRTProduct h f g
          (a + (i : ZMod (m * n))) (b + (j : ZMod (m * n)))‖ ≤
      (C₁ * C₂) *
        (((m * n : ℕ) : ℝ) *
            (1 + Real.log ((m * n : ℕ) : ℝ)) ^ 2 +
          ((L₁ : ℝ) + (L₂ : ℝ)) *
            (1 + Real.log ((m * n : ℕ) : ℝ))) := by
  apply norm_sum_box_le_of_fourier2_bound
      (zmodCRTProduct h f g) (C₁ * C₂) (mul_nonneg hC₁ hC₂)
  · rw [zmodFourier2_crtProduct]
    simp [zmodCRTFirstFrequency, zmodCRTSecondFrequency, hfzero, hgzero]
  · intro k l hkl
    exact norm_zmodFourier2_crtProduct_le_of_local_bounds
      h f g C₁ C₂ hC₁ hC₂ hfzero hgzero hfbound hgbound k l hkl

end
end PellPaper
