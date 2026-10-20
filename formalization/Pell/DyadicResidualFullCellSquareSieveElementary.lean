import Pell.DyadicResidualFullCellSquareSieve
import Pell.IntrinsicOddHomogeneousPolynomialSquareSieveElementary
import Pell.FullCellElementarySieveEnvelope

/-!
# The manuscript square sieve for the balanced residual filters

Each actual odd eliminant is placed in reduced coordinates and passed to the
same parameterized square-sieve estimate used by the standalone lemma.
-/

namespace PellPaper

open Filter
open scoped BigOperators MatrixGroups

noncomputable section

private theorem abs_coeff_rawPell_twoLayerEliminant_le_fullCellHeight_elementary
    (b HF : ℕ) (f' : twoLayerFormIndex b → ℤ) (h : ℤ)
    (hh : h ∈ ({1, -1, 2, -2} : Finset ℤ))
    (hf' : ∀ ab, |f' ab| ≤ (HF : ℤ)) (e : Fin 2 →₀ ℕ) :
    |(twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h).coeff e| ≤
      ((12 * (b + 1) * HF ^ 2 : ℕ) : ℤ) := by
  have hg : ∀ a t, |rawPellQuadraticLinearCoefficients a t| ≤ (1 : ℤ) := by
    intro a t
    fin_cases a <;> fin_cases t <;>
      norm_num [rawPellQuadraticLinearCoefficients]
  have hh' : |h| ≤ (2 : ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl <;> norm_num
  have hcoeff := abs_coeff_twoLayerEliminant_le b f'
    rawPellQuadraticLinearCoefficients h (HF : ℤ) 1
    (by positivity) (by norm_num) hf' hg e
  calc
    |(twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h).coeff e| ≤
        6 * ((b : ℤ) + 1) * |h| * (HF : ℤ) ^ 2 * 1 := hcoeff
    _ = (6 * ((b : ℤ) + 1) * (HF : ℤ) ^ 2) * |h| := by ring
    _ ≤ (6 * ((b : ℤ) + 1) * (HF : ℤ) ^ 2) * 2 := by
      exact mul_le_mul_of_nonneg_left hh' (by positivity)
    _ = ((12 * (b + 1) * HF ^ 2 : ℕ) : ℤ) := by
      push_cast
      ring

private theorem fullCell_reduced_coordinate_le_elementary
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) :
    let mu := firstSlopeSupNorm U V M z
    let delta := M / (U * V)
    4 / mu ≤ 4 * (U + V) ∧ 4 * mu / delta ≤ 4 * (U + V) := by
  dsimp only
  let mu := firstSlopeSupNorm U V M z
  let delta := M / (U * V)
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hmu : 0 < mu := firstSlopeSupNorm_pos U V M z hU hV hMpos
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hrecip := reciprocalFirstSlopeSupNorm_le_add U V M z hU hV hM
  have hA : 4 / mu ≤ 4 * (U + V) := by
    calc
      4 / mu = 4 * reciprocalFirstSlopeSupNorm U V M z := by
        simp only [reciprocalFirstSlopeSupNorm, mu]
        ring
      _ ≤ 4 * (U + V) := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hsq : mu ^ 2 ≤ delta := by
    have hmule := firstSlopeSupNorm_le_sqrt U V M z hU hV hMpos
    have hsqrt := Real.sq_sqrt hdelta.le
    change mu ≤ Real.sqrt delta at hmule
    nlinarith [Real.sqrt_nonneg delta]
  have hBA : 4 * mu / delta ≤ 4 / mu := by
    apply (div_le_div_iff₀ hdelta hmu).mpr
    nlinarith
  exact ⟨hA, hBA.trans hA⟩


private theorem eventually_fullCell_oneFilter_le_elementary :
    ∀ᶠ N : ℕ in atTop,
      ∀ (U V M mu delta A B : ℝ) (W : SL(2, ℤ))
        (T : Finset (Fin 2 → ℤ)) (b HF : ℕ)
        (f' : twoLayerFormIndex b → ℤ) (h : ℤ),
        0 < U → 0 < V → 0 < M → 0 < mu → 0 < delta →
        mu ^ 2 ≤ delta →
        (∀ a c, |((W a c : ℤ) : ℝ)| ≤ 6 * M * (U + V)) →
        sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A B →
        ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M →
        ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu →
        ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta →
        A ≤ 4 * (U + V) → B ≤ 4 * (U + V) →
        h ∈ ({1, -1, 2, -2} : Finset ℤ) →
        0 < HF → (∀ ab, |f' ab| ≤ (HF : ℤ)) →
        let d : ℕ := 2 * b + 1
        let Hraw : ℕ := 12 * (b + 1) * HF ^ 2
        let L : ℝ := 6 * M * (U + V)
        let HK : ℕ := binaryLinearSubstitutionNatHeight d (Hraw : ℝ) L
        let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
        Real.log Wval ≤ (Real.log 2 / 16) * (N : ℝ) →
        (((T.filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
          MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ)) ≤
          fullCellElementarySieveEnvelope N d U V M mu := by
  filter_upwards
    [eventually_fullCell_oddHomogeneousPolynomial_filter_le_elementary]
      with N hsieve
  intro U V M mu delta A B W T b HF f' h hU hV hM hmu hdelta hsq
    hW hCsubset harea hsideA hsideB hcoordA hcoordB hh hHF hf'
  dsimp only
  intro hWvalBudget
  let d : ℕ := 2 * b + 1
  let K : MvPolynomial (Fin 2) ℤ :=
    twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h
  let Hraw : ℕ := 12 * (b + 1) * HF ^ 2
  let L : ℝ := 6 * M * (U + V)
  let HK : ℕ := binaryLinearSubstitutionNatHeight d (Hraw : ℝ) L
  have hKhom : K.IsHomogeneous d :=
    twoLayerEliminant_isHomogeneous b f' rawPellQuadraticLinearCoefficients h
  have hKcoeffR : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ (Hraw : ℝ) := by
    intro e
    exact_mod_cast
      abs_coeff_rawPell_twoLayerEliminant_le_fullCellHeight_elementary b HF f' h hh hf' e
  have hKWcoeff : ∀ e,
      |(binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K).coeff e| ≤
        (HK : ℤ) := by
    intro e
    exact abs_coeff_binaryLinearSubstitution_le_natHeight
      (W : Matrix (Fin 2) (Fin 2) ℤ) K d (Hraw : ℝ) L hKhom hKcoeffR
        (by simpa only [L] using hW) e
  have hHK : 0 < HK := binaryLinearSubstitutionNatHeight_pos d (Hraw : ℝ) L
  exact hsieve U V M mu delta A B W T K d HK
    hU hV hM hmu hdelta hsq hKhom ⟨b, rfl⟩ hHK hKWcoeff
    hCsubset harea hsideA hsideB hcoordA hcoordB hWvalBudget

/-- Uniformly in the sieve scale, one reduced basis bounds all four literal
nonzero-square target filters in a full dyadic source/target cell.  The
matrix is selected after `i,M,k` and before `theta,Y,sourceIndex,b,f'` and is
reused for every signed level. -/
theorem eventually_sum_full_dyadicTarget_eliminant_squareFilters_le_elementary :
    ∀ᶠ N : ℕ in atTop,
      ∀ (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (k : ℤ),
        0 < M → k ∈ targetSlopeIntegerCenters (M : ℝ) →
      ∀ (theta : ℝ) (Y sourceIndex b HF : ℕ)
        (f' : twoLayerFormIndex b → ℤ),
        0 < HF → (∀ ab, |f' ab| ≤ (HF : ℤ)) →
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
        let delta := (M : ℝ) / (U * V)
        let B := 4 * mu / delta
        let T := dyadicSourceTargetImage theta Y i M sourceIndex k
        1 ≤ B →
        fullCellResidualSieveBudgets N i M b HF →
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
  filter_upwards [eventually_fullCell_oneFilter_le_elementary,
    eventually_ge_atTop 4] with N hOneFilter hN
  intro i M k hM hk
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
  let delta := (M : ℝ) / (U * V)
  let A := 4 / mu
  let B := 4 * mu / delta
  obtain ⟨W, _hfirst, hentry, _hcoords, hcover⟩ :=
    exists_reduced_dyadicSourceTargetImage_cover_with_entry_bound i M k hM hk
  intro theta Y sourceIndex b HF f' hHF hf'
  dsimp only
  intro hfull hbudgets
  let T := dyadicSourceTargetImage theta Y i M sourceIndex k
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmu : 0 < mu := firstSlopeSupNorm_pos U V (M : ℝ) (k : ℝ) hU hV hMr
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsq : mu ^ 2 ≤ delta := by
    have hmule := firstSlopeSupNorm_le_sqrt U V (M : ℝ) (k : ℝ) hU hV hMr
    have hsqrt := Real.sq_sqrt hdelta.le
    change mu ≤ Real.sqrt delta at hmule
    nlinarith [Real.sqrt_nonneg delta]
  have hEnvelope :
      0 ≤ fullCellElementarySieveEnvelope N (2 * b + 1)
        U V (M : ℝ) mu :=
    fullCellElementarySieveEnvelope_nonnegative N (2 * b + 1)
      U V (M : ℝ) mu hN hU hV hMr hmu
  change (∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
      ((T.filter fun y =>
        IsSquare (MvPolynomial.eval y
          (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
        MvPolynomial.eval y
          (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ)) ≤
    4 * fullCellElementarySieveEnvelope N (2 * b + 1)
      U V (M : ℝ) mu
  by_cases hT : T.Nonempty
  · obtain ⟨_hcard, _hprimitive, _hrecover, hCsubset, _hA, _hthin,
        hfullBudgets⟩ := hcover theta Y sourceIndex
    obtain ⟨harea, hsideA, hsideB, _hperimeter⟩ := hfullBudgets hT hfull
    obtain ⟨hcoordA, hcoordB⟩ :=
      fullCell_reduced_coordinate_le_elementary U V (M : ℝ) (k : ℝ) hU hV hMone
    obtain ⟨hWvalBudget, _hcertBudget⟩ := hbudgets
    have hEach : ∀ h ∈ ({1, -1, 2, -2} : Finset ℤ),
        (((T.filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
          MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ)) ≤
          fullCellElementarySieveEnvelope N (2 * b + 1)
            U V (M : ℝ) mu := by
      intro h hh
      apply hOneFilter U V (M : ℝ) mu delta A B W T b HF f' h
        hU hV hMr hmu hdelta hsq
      · simpa only [U, V] using hentry
      · simpa only [T, A, B] using hCsubset
      · simpa only [A, B, U, V] using harea
      · simpa only [A] using hsideA
      · simpa only [B] using hsideB
      · simpa only [A] using hcoordA
      · simpa only [B] using hcoordB
      · exact hh
      · exact hHF
      · exact hf'
      · simpa only [U, V] using hWvalBudget
    calc
      (∑ h ∈ ({1, -1, 2, -2} : Finset ℤ),
          ((T.filter fun y =>
            IsSquare (MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
            MvPolynomial.eval y
              (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ)) ≤
          ∑ _h ∈ ({1, -1, 2, -2} : Finset ℤ),
            fullCellElementarySieveEnvelope N (2 * b + 1)
              U V (M : ℝ) mu := Finset.sum_le_sum fun h hh => hEach h hh
      _ = 4 * fullCellElementarySieveEnvelope N (2 * b + 1)
              U V (M : ℝ) mu := by norm_num
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [hTempty]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) hEnvelope



end

end PellPaper

