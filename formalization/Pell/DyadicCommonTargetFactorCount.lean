import Pell.DyadicRawTargetZeroCount
import Pell.TwoLayerCommonFactorSelection

/-!
# Counting the actual selected common-target zero branch

A nonzero original two-layer coefficient vector constructs its bounded
integral common-target and residual factors through the accepted selection
theorem. The new raw dyadic count bounds the entire selected target-zero
subfamily by `96*Q*n`, where n is the original target degree. No chosen
factor or source-fibre capacity is supplied by the caller. This does not
bound the residual square branch or the whole original solution family.
-/

namespace PellPaper

/-- Select actual bounded factors of the original coefficient vector and
simultaneously count the full raw dyadic zero branch of that selected
target factor. All algebraic, height and residual-nonvanishing conclusions
of the existing selection theorem are retained. -/
theorem exists_bounded_twoLayer_common_factor_with_dyadic_zero_count
    (n : ℕ) (f : twoLayerFormIndex n → ℤ) (hf₀ : f ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H)
    (θ Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ q ∈ S, DyadicFactorCondition θ Y q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hbox : ∀ q ∈ S, q ∈ dyadicBox i) :
    ∃ (d b : ℕ) (D : MvPolynomial (Fin 2) ℤ) (f' : twoLayerFormIndex b → ℤ),
      d + b = n ∧ D ≠ 0 ∧ D.IsHomogeneous d ∧ f' ≠ 0 ∧
      (∀ a : Fin 2, twoLayerBinaryPolynomial n f a =
        D * twoLayerBinaryPolynomial b f' a) ∧
      (∀ e, |((D.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
      (∀ ab, |((f' ab : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
      (∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
        MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 0) ≠ 0 ∨
          MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 1) ≠ 0) ∧
      (∀ lambda y : ℤ × ℤ, twoLayerFormEval n f (lambda, y) =
        MvPolynomial.eval ![y.1, y.2] D * twoLayerFormEval b f' (lambda, y)) ∧
      ((S.filter fun q =>
        MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card : ℝ) ≤
          96 * Q * (n : ℝ) := by
  classical
  obtain ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf', hcomponents, heval⟩ :=
    exists_bounded_twoLayer_common_factor n f hf₀ H hH hf
  refine ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf', hcomponents, heval, ?_⟩
  have hc := card_filter_dyadic_raw_target_zeros_le_ninetySix_mul_Q_mul_degree
    θ Q Y i hY hQ hxQ D d hD hD0 S hcond hbox
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast (show d ≤ n by omega)
  exact hc.trans (mul_le_mul_of_nonneg_left hdn (by linarith))

end PellPaper
