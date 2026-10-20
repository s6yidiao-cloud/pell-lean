import Pell.DyadicResidualSquareCount
import Pell.DyadicResidualFullCellSquareSieveElementary

/-!
# Full-cell square-sieve count for literal dyadic source tuples

This file inserts the full-cell target-vector square sieve into the existing
source-tuple residual reduction.  The target map is used only as the one-way
cover already present in that reduction; no tuple/image cardinality identity
is asserted.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- In the full reduced-width branch, the existing common-factor reduction
and the literal target image give a source-tuple bound with the exact residual
factor `2` and four-filter factor `4`.  All algebraic factor-selection
conclusions needed downstream are retained.

The single eventual threshold precedes every source form, dyadic cell,
coefficient height, budget, and tuple family. -/
theorem eventually_exists_bounded_twoLayer_common_factor_with_full_dyadic_count_elementary :
    ∀ᶠ N : ℕ in atTop,
      ∀ (n : ℕ) (f : twoLayerFormIndex n → ℤ) (_hf₀ : f ≠ 0)
        (H : ℝ) (_hH : 0 ≤ H) (_hf : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H)
        (theta Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M j : ℕ) (k : ℤ),
        0 < M → k ∈ targetSlopeIntegerCenters (M : ℝ) →
        2 ≤ Y → 2 ≤ Q →
        ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (2 * Q) →
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
        let delta := (M : ℝ) / (U * V)
        let HF : ℕ := positiveNatCeil
          ((2 : ℝ) ^ n * ((n : ℝ) + 1) * H)
        1 ≤ 4 * mu / delta →
        (∀ b ≤ n, fullCellResidualSieveBudgets N i M b HF) →
        ∀ (S : Finset (ℕ × ℕ × ℕ × ℕ)),
        S ⊆ dyadicSourceTargetTupleCell theta Y i M j k →
        (∀ q ∈ S, twoLayerFormEval n f
          (((q.1 : ℤ), (q.2.1 : ℤ)),
            ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0) →
        ∃ (d b : ℕ) (D : MvPolynomial (Fin 2) ℤ)
            (f' : twoLayerFormIndex b → ℤ),
          d + b = n ∧ D ≠ 0 ∧ D.IsHomogeneous d ∧ f' ≠ 0 ∧
          (∀ a : Fin 2, twoLayerBinaryPolynomial n f a =
            D * twoLayerBinaryPolynomial b f' a) ∧
          (∀ e, |((D.coeff e : ℤ) : ℝ)| ≤
            (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
          (∀ ab, |((f' ab : ℤ) : ℝ)| ≤
            (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
          (∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
            MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 0) ≠ 0 ∨
              MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 1) ≠ 0) ∧
          (∀ lambda y : ℤ × ℤ, twoLayerFormEval n f (lambda, y) =
            MvPolynomial.eval ![y.1, y.2] D *
              twoLayerFormEval b f' (lambda, y)) ∧
          ((S.filter fun q =>
            MvPolynomial.eval
              ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card : ℝ) ≤
              96 * Q * (n : ℝ) ∧
          (S.card : ℝ) ≤ 96 * Q * (n : ℝ) +
            8 * fullCellElementarySieveEnvelope N (2 * b + 1)
              U V (M : ℝ) mu := by
  filter_upwards
    [eventually_sum_full_dyadicTarget_eliminant_squareFilters_le_elementary]
      with N hfullCount
  intro n f hf₀ H hH hf theta Q Y i M j k hM hk hY hQ hxQ
  dsimp only
  intro hfull hbudgets S hS hzero
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
  let delta := (M : ℝ) / (U * V)
  let HF : ℕ := positiveNatCeil
    ((2 : ℝ) ^ n * ((n : ℝ) + 1) * H)
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
  have hT : ∀ q ∈ S,
      ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] ∈ T := by
    intro q hq
    have hcell := hS hq
    have hmem := Finset.mem_filter.mp hcell
    exact (mem_dyadicSourceTargetImage_iff theta Y i M j k _).mpr
      ⟨q, hmem.1, hmem.2, rfl⟩
  obtain ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf',
      hcomponents, heval, hz, hsquare⟩ :=
    exists_bounded_twoLayer_common_factor_with_dyadic_square_count
      n f hf₀ H hH hf theta Q Y i hY hQ hxQ S hcond hbox hzero T hT
  have hsourceHeightLe :
      (2 : ℝ) ^ n * ((n : ℝ) + 1) * H ≤ (HF : ℝ) := by
    exact le_positiveNatCeil _
  have hHF : 0 < HF := positiveNatCeil_pos _
  have hHf'Z : ∀ ab, |f' ab| ≤ (HF : ℤ) := by
    intro ab
    have hab : |((f' ab : ℤ) : ℝ)| ≤ (HF : ℝ) :=
      (hHf' ab).trans hsourceHeightLe
    exact_mod_cast hab
  have hb_le : b ≤ n := by omega
  have hsum :
      (∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        ((T.filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant b f'
              rawPellQuadraticLinearCoefficients h)) ∧
          MvPolynomial.eval y
            (twoLayerEliminant b f'
              rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ)) ≤
        4 * fullCellElementarySieveEnvelope N (2 * b + 1)
          U V (M : ℝ) mu := by
    have h := hfullCount i M k hM hk theta Y j b HF f' hHF hHf'Z
    simpa only [U, V, mu, delta, T, HF] using
      h hfull (hbudgets b hb_le)
  refine ⟨d, b, D, f', hdb, hD0, hD, hf'0, hfactor, hHD, hHf',
    hcomponents, heval, hz, ?_⟩
  calc
    (S.card : ℝ) ≤ 96 * Q * (n : ℝ) +
        2 * ∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
          ((T.filter fun y =>
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant b f'
                rawPellQuadraticLinearCoefficients h)) ∧
            MvPolynomial.eval y
              (twoLayerEliminant b f'
                rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ) := hsquare
    _ ≤ 96 * Q * (n : ℝ) +
        2 * (4 * fullCellElementarySieveEnvelope N (2 * b + 1)
          U V (M : ℝ) mu) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = 96 * Q * (n : ℝ) +
        8 * fullCellElementarySieveEnvelope N (2 * b + 1)
          U V (M : ℝ) mu := by ring

end

end PellPaper


