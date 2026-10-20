import Pell.DyadicRawPairPrimitivity
import Pell.RawPellSurface
import Pell.SignedLevelPrimitiveProjection
import Pell.DyadicCommonTargetFactorCount

/-!
# Actual dyadic tuples and the four residual square-target filters

The literal raw source/target map preserves the original tuple count.
Primitivity and the signed Pell surface are derived from the actual factor
condition, not supplied as representation assumptions. The selected
common-target zero branch is counted once by 96*Q*n; the rest projects
to target vectors where one of the four actual residual eliminants has a
nonzero square evaluation.

This is a finite algebraic counting reduction. The target cover is any
supplied finite set, so no coarse rectangular enlargement or loss of
slope-cell geometry is built into the statement. No uniform square sieve,
coordinate-height budget or headline theorem is claimed.
-/

namespace PellPaper
noncomputable section
open scoped BigOperators

/-- An actual raw dyadic family on the original source-linear zero set
retains its target-zero tuples and projects the residual tuples over the
four signed Pell levels. The actual condition supplies both primitive
pairs and the literal surface equation internally. -/
theorem card_dyadic_twoLayer_solutions_le_target_zeros_add_twice_sum_squares
    (n b : ℕ) (f : twoLayerFormIndex n → ℤ) (f' : twoLayerFormIndex b → ℤ)
    (D : MvPolynomial (Fin 2) ℤ)
    (hfactor : ∀ a : Fin 2, twoLayerBinaryPolynomial n f a =
      D * twoLayerBinaryPolynomial b f' a)
    (hcomponents : ∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
      MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 0) ≠ 0 ∨
        MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 1) ≠ 0)
    (θ : ℝ) (Y : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ q ∈ S, DyadicFactorCondition θ Y q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hzero : ∀ q ∈ S, twoLayerFormEval n f
      (((q.1 : ℤ), (q.2.1 : ℤ)), ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0)
    (T : Finset (Fin 2 → ℤ))
    (hT : ∀ q ∈ S, ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] ∈ T) :
    S.card ≤ (S.filter fun q =>
      MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card +
      2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        (T.filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
          MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card := by
  classical
  let P := S.map dyadicFactorTupleToRawPellVectorPointEmbedding
  have hPcard : P.card = S.card := Finset.card_map _
  have hPzero :
      (P.filter fun p => MvPolynomial.eval p.2 D = 0).card =
        (S.filter fun q =>
          MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card := by
    simp only [P, Finset.filter_map, Finset.card_map, Function.comp_def,
      dyadicFactorTupleToRawPellVectorPointEmbedding_apply]
  have hP :
      ∀ p ∈ P, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
        p.1 0 * MvPolynomial.eval p.2 (twoLayerBinaryPolynomial n f 0) +
          p.1 1 * MvPolynomial.eval p.2 (twoLayerBinaryPolynomial n f 1) = 0 ∧
        IsSignedDyadicDifference
          (quadraticLinearFormEval rawPellQuadraticLinearCoefficients p.1 p.2) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    simp only [dyadicFactorTupleToRawPellVectorPointEmbedding_apply]
    obtain ⟨hs, ht⟩ := dyadicFactorCondition_primitive_raw_pairs (hcond q hq)
    refine ⟨hs, ht, ?_, ?_⟩
    · simpa only [twoLayerFormEval_eq_binaryPolynomial, Matrix.cons_val_zero,
        Matrix.cons_val_one] using hzero q hq
    · rw [quadraticLinearFormEval_rawPell]
      exact isSignedDyadicDifference_of_dyadicFactorCondition (hcond q hq) (by ring)
  have hc := card_signed_surface_solutions_le_common_factor_zeros_add_twice_sum_squares
    rawPellQuadraticLinearCoefficients
    (twoLayerBinaryPolynomial n f 0) (twoLayerBinaryPolynomial n f 1) D
    (twoLayerBinaryPolynomial b f' 0) (twoLayerBinaryPolynomial b f' 1)
    (hfactor 0) (hfactor 1) P T hP
    (by intro p hp _; exact hcomponents p.2 (hP p hp).2.1)
    (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
      simpa only [dyadicFactorTupleToRawPellVectorPointEmbedding_apply] using hT q hq)
  rw [hPcard, hPzero] at hc
  exact hc

/-- From the original bounded coefficients, select actual factors and
bound the whole actual dyadic solution family by 96*Q*n plus the four
residual square-target counts. All prior bounded selection conclusions
and the separate selected-zero-filter bound are retained. -/
theorem exists_bounded_twoLayer_common_factor_with_dyadic_square_count
    (n : ℕ) (f : twoLayerFormIndex n → ℤ) (hf₀ : f ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H)
    (θ Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ q ∈ S, DyadicFactorCondition θ Y q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hbox : ∀ q ∈ S, q ∈ dyadicBox i)
    (hzero : ∀ q ∈ S, twoLayerFormEval n f
      (((q.1 : ℤ), (q.2.1 : ℤ)), ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0)
    (T : Finset (Fin 2 → ℤ))
    (hT : ∀ q ∈ S, ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] ∈ T) :
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
          96 * Q * (n : ℝ) ∧
      (S.card : ℝ) ≤ 96 * Q * (n : ℝ) +
        2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
          ((T.filter fun y =>
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
            MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ) := by
  classical
  obtain ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf', hcomponents,
      heval, hz⟩ :=
    exists_bounded_twoLayer_common_factor_with_dyadic_zero_count
      n f hf₀ H hH hf θ Q Y i hY hQ hxQ S hcond hbox
  refine ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf', hcomponents,
    heval, hz, ?_⟩
  have hc := card_dyadic_twoLayer_solutions_le_target_zeros_add_twice_sum_squares
    n b f f' D hfactor hcomponents θ Y S hcond hzero T hT
  have hcR :
      (S.card : ℝ) ≤
        ((S.filter fun q =>
          MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card : ℝ) +
        2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
          ((T.filter fun y =>
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
            MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ) := by
    exact_mod_cast hc
  exact hcR.trans (add_le_add hz (le_refl _))

end
end PellPaper
