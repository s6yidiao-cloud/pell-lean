import Pell.DyadicResidualSquareCount
import Pell.ReducedDyadicTargetCover

/-!
# Strict-thin residual square count on literal dyadic target images

An actual source/target tuple subfamily supplies its factor condition, dyadic
box membership, and literal target-image cover internally.  In the strict
reduced-width branch the image contains at most two primitive targets, so the
four residual square filters contribute at most sixteen after the existing
factor-zero contribution.  No tuple/image cardinality identity or polynomial
coordinate transport is used.
-/

namespace PellPaper

noncomputable section
open scoped BigOperators

/-- In a strict thin reduced cell, the existing common-factor reduction and
the literal target image give the scalar bound `96 * Q * n + 16`.  All
algebraic factor-selection conclusions needed downstream are retained. -/
theorem exists_bounded_twoLayer_common_factor_with_thin_dyadic_count
    (n : ℕ) (f : twoLayerFormIndex n → ℤ) (hf₀ : f ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H)
    (theta Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M j : ℕ) (k : ℤ)
    (hM : 0 < M) (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (hthin : 4 * firstSlopeSupNorm
        ((2 ^ i.2.2.1 : ℕ) : ℝ) ((2 ^ i.2.2.2 : ℕ) : ℝ)
        (M : ℝ) (k : ℝ) /
        ((M : ℝ) /
          (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))) < 1)
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hS : S ⊆ dyadicSourceTargetTupleCell theta Y i M j k)
    (hzero : ∀ q ∈ S, twoLayerFormEval n f
      (((q.1 : ℤ), (q.2.1 : ℤ)), ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0) :
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
      ((S.filter fun q ↦
        MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card : ℝ) ≤
          96 * Q * (n : ℝ) ∧
      (S.card : ℝ) ≤ 96 * Q * (n : ℝ) + 16 := by
  classical
  let T := dyadicSourceTargetImage theta Y i M j k
  have hcond : ∀ q ∈ S,
      DyadicFactorCondition theta Y q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    intro q hq
    have hcell := hS hq
    have hlocal : q ∈ dyadicFactorBoxLocalRatioCell theta Y i M j :=
      (Finset.mem_filter.mp hcell).1
    have hambient := (mem_dyadicFactorBoxLocalRatioCell hlocal).1
    exact mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hambient).1
  have hbox : ∀ q ∈ S, q ∈ dyadicBox i := by
    intro q hq
    have hcell := hS hq
    have hlocal : q ∈ dyadicFactorBoxLocalRatioCell theta Y i M j :=
      (Finset.mem_filter.mp hcell).1
    have hambient := (mem_dyadicFactorBoxLocalRatioCell hlocal).1
    exact (Finset.mem_inter.mp hambient).2
  have hT : ∀ q ∈ S, ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] ∈ T := by
    intro q hq
    have hcell := hS hq
    have hmem := Finset.mem_filter.mp hcell
    exact (mem_dyadicSourceTargetImage_iff theta Y i M j k _).mpr
      ⟨q, hmem.1, hmem.2, rfl⟩
  have hTcard : T.card ≤ 2 := by
    obtain ⟨W, _, hcover⟩ := exists_reduced_dyadicSourceTargetImage_cover i M k hM
    obtain ⟨_, _, _, _, _, hcard, _⟩ := hcover theta Y j
    exact hcard hthin
  obtain ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf', hcomponents,
      heval, hz, hsquare⟩ :=
    exists_bounded_twoLayer_common_factor_with_dyadic_square_count
      n f hf₀ H hH hf theta Q Y i hY hQ hxQ S hcond hbox hzero T hT
  refine ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf', hcomponents,
    heval, hz, ?_⟩
  have hfilter (h : ℤ) :
      ((T.filter fun y ↦
        IsSquare (MvPolynomial.eval y
          (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
        MvPolynomial.eval y
          (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ) ≤ 2 := by
    exact_mod_cast (Finset.card_filter_le _ _).trans hTcard
  have hsum :
      ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        ((T.filter fun y ↦
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
          MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ) ≤ 8 := by
    calc
      _ ≤ ∑ _h ∈ ({1, -1, 2, -2} : Finset ℤ), (2 : ℝ) := by
        exact Finset.sum_le_sum fun h _ ↦ hfilter h
      _ = 8 := by norm_num
  calc
    (S.card : ℝ) ≤ 96 * Q * (n : ℝ) +
        2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
          ((T.filter fun y ↦
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
            MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ) := hsquare
    _ ≤ 96 * Q * (n : ℝ) + 2 * 8 := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num))
    _ = 96 * Q * (n : ℝ) + 16 := by ring

end
end PellPaper
