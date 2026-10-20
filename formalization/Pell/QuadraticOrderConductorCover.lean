import Pell.QuadraticOrderFundamentalSquare
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A finite conductor cover for nonnegative order-discriminant weights

Existence of a fundamental discriminant and a square conductor gives a
finite nonnegative sum bound with the exact scaled cutoff `D₀ < X/f²`.
Representations need not be chosen uniquely. No estimate for class numbers
or L-values is assumed or concluded by this generic cover.
-/

namespace PellPaper

open scoped BigOperators

/-- All order-discriminant weights are covered by the conductor sum, with
the literal strict scaled cutoff. This remains valid for all real `X`,
including nonpositive and nonintegral cutoffs. -/
theorem sum_orderDiscriminantsBelow_le_conductor_sum
    (w : ℕ → ℝ) (hw : ∀ D, 0 ≤ w D) (X : ℝ) :
    (∑ D ∈ orderDiscriminantsBelow X, w D) ≤
      ∑ f ∈ Finset.Icc 1 ⌈X⌉₊,
        ∑ D₀ ∈ fundamentalDiscriminantsBelow (X / (f : ℝ) ^ 2),
          w (D₀ * f ^ 2) := by
  classical
  let S : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.Icc 1 ⌈X⌉₊).sigma
      (fun f => fundamentalDiscriminantsBelow (X / (f : ℝ) ^ 2))
  let F : (Σ _ : ℕ, ℕ) → ℕ := fun t => t.2 * t.1 ^ 2
  have hcover : orderDiscriminantsBelow X ⊆ S.image F := by
    intro D hD
    obtain ⟨hD, hDX⟩ := mem_orderDiscriminantsBelow.mp hD
    obtain ⟨D₀, f, hfund, hf, hfactor⟩ :=
      exists_positiveFundamental_mul_sq_of_positiveQuadraticOrderDiscriminant hD
    have hfpos : 0 < (f : ℝ) := by exact_mod_cast hf
    have hfsq : f ≤ f ^ 2 := le_self_pow hf (by decide : 2 ≠ 0)
    have hfD : f ≤ D := by
      calc
        f ≤ f ^ 2 := hfsq
        _ ≤ D₀ * f ^ 2 := Nat.le_mul_of_pos_left _ (by have := hfund.1; omega)
        _ = D := hfactor.symm
    have hfX : f ≤ ⌈X⌉₊ := by
      have hDceil : D < ⌈X⌉₊ := Nat.lt_ceil.mpr hDX
      omega
    have hscaled : (D₀ : ℝ) < X / (f : ℝ) ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hfpos)).mpr
      exact_mod_cast (show ((D₀ * f ^ 2 : ℕ) : ℝ) < X from hfactor ▸ hDX)
    apply Finset.mem_image.mpr
    refine ⟨⟨f, D₀⟩, ?_, hfactor.symm⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hf, hfX⟩,
      mem_fundamentalDiscriminantsBelow.mpr ⟨hfund, hscaled⟩⟩
  calc
    (∑ D ∈ orderDiscriminantsBelow X, w D) ≤ ∑ D ∈ S.image F, w D :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun D _ _ => hw D)
    _ ≤ ∑ t ∈ S, w (F t) := Finset.sum_image_le_of_nonneg (fun D _ => hw D)
    _ = ∑ f ∈ Finset.Icc 1 ⌈X⌉₊,
        ∑ D₀ ∈ fundamentalDiscriminantsBelow (X / (f : ℝ) ^ 2),
          w (D₀ * f ^ 2) := by
      exact Finset.sum_sigma _ _ _

end PellPaper
