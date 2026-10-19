import Pell.DyadicResidualFullCellSquareSieve
import Pell.ElementaryQuadraticCharacterSieveBypass
import Pell.FullCellElementarySieveEnvelope

/-!
# Unconditional elementary full-cell square sieve

This module replaces the higher-degree Weil input in the full-cell residual
sieve by the unconditional projective triangle bound.  The resulting local
Fourier error is `O(N^3)` and is independent of the polynomial degree.
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
        let HJ : ℕ := 2 ^ d * (d + 1) * HK
        let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
        Real.log Wval ≤ (Real.log 2 / 16) * (N : ℝ) →
        (∀ j : ℕ, Odd j → 0 < j → j ≤ d →
          fullCellCertificateLogMajorant d HK j +
              2 * Real.log (HJ : ℝ) ≤
            (Real.log 2 / 8) * (N : ℝ)) →
        (((T.filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h)) ∧
          MvPolynomial.eval y
            (twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h) ≠ 0).card : ℝ)) ≤
          fullCellElementarySieveEnvelope N d U V M mu := by
  filter_upwards
    [eventually_squareSieve_oddHomogeneous_polynomial_rectangle_le_trivial,
      eventually_ge_atTop 4]
      with N hsieve hN
  intro U V M mu delta A B W T b HF f' h hU hV hM hmu hdelta hsq
    hW hCsubset harea hsideA hsideB hcoordA hcoordB hh hHF hf'
  dsimp only
  intro hWvalBudget hcertBudget
  let d : ℕ := 2 * b + 1
  let K : MvPolynomial (Fin 2) ℤ :=
    twoLayerEliminant b f' rawPellQuadraticLinearCoefficients h
  let KW : MvPolynomial (Fin 2) ℤ :=
    binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K
  let Hraw : ℕ := 12 * (b + 1) * HF ^ 2
  let L : ℝ := 6 * M * (U + V)
  let HK : ℕ := binaryLinearSubstitutionNatHeight d (Hraw : ℝ) L
  let HJ : ℕ := 2 ^ d * (d + 1) * HK
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
  let x0 : ℤ := -⌊A⌋
  let y0 : ℤ := -⌊B⌋
  let L₁ : ℕ := (2 * ⌊A⌋ + 1).toNat
  let L₂ : ℕ := (2 * ⌊B⌋ + 1).toNat
  have hd : d = 2 * b + 1 := rfl
  have hKhom : K.IsHomogeneous d := by
    exact twoLayerEliminant_isHomogeneous b f'
      rawPellQuadraticLinearCoefficients h
  have hKcoeffR : ∀ e, |((K.coeff e : ℤ) : ℝ)| ≤ (Hraw : ℝ) := by
    intro e
    exact_mod_cast
      abs_coeff_rawPell_twoLayerEliminant_le_fullCellHeight_elementary b HF f' h hh hf' e
  have hKWhom : KW.IsHomogeneous d :=
    binaryLinearSubstitution_isHomogeneous _ K d hKhom
  have hKWcoeff : ∀ e, |KW.coeff e| ≤ (HK : ℤ) := by
    intro e
    exact abs_coeff_binaryLinearSubstitution_le_natHeight
      (W : Matrix (Fin 2) (Fin 2) ℤ) K d (Hraw : ℝ) L hKhom hKcoeffR
        (by simpa only [L] using hW) e
  have hHK : 0 < HK := binaryLinearSubstitutionNatHeight_pos d (Hraw : ℝ) L
  have hHJ : 0 < HJ := by dsimp [HJ]; positivity
  have hEnvelope : 0 ≤ fullCellElementarySieveEnvelope N d U V M mu :=
    fullCellElementarySieveEnvelope_nonnegative N d U V M mu hN hU hV hM hmu
  change ((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
      MvPolynomial.eval y K ≠ 0).card : ℝ) ≤
    fullCellElementarySieveEnvelope N d U V M mu
  by_cases hK0 : K = 0
  · simpa [hK0] using hEnvelope
  have hKW0 : KW ≠ 0 :=
    binaryLinearSubstitution_sl2_ne_zero W hK0
  obtain ⟨a, R, J, m, j, hfactor, ha, _hasq, _haHeight, hR0, hJ0,
      hRhom, hJhom, hdegree, hj, hjpos, _hprimitive, hJcoeff,
      hDelta0, hDeltaLog⟩ :=
    exists_homogeneous_square_factor_with_bounded_resultant_certificate
      KW d HK hKWhom hKW0 ⟨b, rfl⟩ hHK hKWcoeff
  let Delta : ℤ := 2 * a * binaryProjectiveDerivativeResultant J j
  have hjle : j ≤ d := by omega
  have hDeltaLog' :
      Real.log (Delta.natAbs : ℝ) ≤
        fullCellCertificateLogMajorant d HK j := by
    simpa only [Delta, fullCellCertificateLogMajorant] using hDeltaLog
  have hDeltaStrong :
      fullCellCertificateLogMajorant d HK j + 2 * Real.log (HJ : ℝ) ≤
        (Real.log 2 / 8) * (N : ℝ) :=
    hcertBudget j hj hjpos hjle
  have hDeltaLinear :
      Real.log (Delta.natAbs : ℝ) + 2 * Real.log (HJ : ℝ) ≤
        (Real.log 2 / 8) * (N : ℝ) :=
    (add_le_add hDeltaLog' (le_refl _)).trans hDeltaStrong
  have hlogHJ : 0 ≤ Real.log (HJ : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hHJ.ne'))
  have hDeltaHigher :
      Real.log (Delta.natAbs : ℝ) ≤
        (Real.log 2 / 8) * (N : ℝ) := by
    linarith
  have haDelta : a ∣ Delta := by
    refine ⟨2 * binaryProjectiveDerivativeResultant J j, ?_⟩
    dsimp [Delta]
    ring
  have hresultantDelta : binaryProjectiveDerivativeResultant J j ∣ Delta := by
    refine ⟨2 * a, ?_⟩
    dsimp [Delta]
    ring
  let fxy : ℕ × ℕ → ℤ := fun xy =>
    MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] KW
  let rxy : ℕ × ℕ → ℤ := fun xy =>
    MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] R
  have hfactorEval : ∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      fxy xy = a * (rxy xy) ^ 2 *
        MvPolynomial.eval
          ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J := by
    intro xy _hxy
    dsimp only [fxy, rxy]
    rw [hfactor]
    simp
  have hKWcoeffR : ∀ e, |((KW.coeff e : ℤ) : ℝ)| ≤ (HK : ℝ) := by
    intro e
    exact_mod_cast hKWcoeff e
  have hsize : ∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      ((fxy xy).natAbs : ℝ) ≤ Wval := by
    intro xy hxy
    have hzmem :
        ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] ∈
          integerSymmetricRectangle A B := by
      rw [integerSymmetricRectangle_eq_map_rangeProduct]
      apply Finset.mem_map.mpr
      refine ⟨xy, ?_, ?_⟩
      · simpa only [L₁, L₂] using hxy
      · simp only [integerSymmetricRectangleRangeEmbedding_apply, x0, y0]
    have hz := (mem_integerSymmetricRectangle A B _).mp hzmem
    have hy : ∀ q : Fin 2,
        |((![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] q : ℤ) : ℝ)| ≤
          4 * (U + V) := by
      intro q
      fin_cases q
      · exact hz.1.trans hcoordA
      · exact hz.2.trans hcoordB
    have hv := abs_eval_homogeneous_binary_le KW d (HK : ℝ)
      (4 * (U + V)) hKWhom (by positivity) (by positivity)
      hKWcoeffR ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] hy
    simpa only [fxy, Wval, Nat.cast_natAbs, Int.cast_abs] using hv
  have hfilteredNat :
      (T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
        MvPolynomial.eval y K ≠ 0).card ≤
      (((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
        fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card := by
    let P : ℤ → Prop := fun z => IsSquare z ∧ z ≠ 0
    have htransport :=
      card_filter_sl2InverseTargetImage_binaryLinearSubstitution W T K P
    have hsubset :
        (sl2InverseTargetImage W T).filter (fun x =>
          P (MvPolynomial.eval x KW)) ⊆
        (integerSymmetricRectangle A B).filter (fun x =>
          P (MvPolynomial.eval x KW)) := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨hCsubset (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    calc
      (T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
          MvPolynomial.eval y K ≠ 0).card =
          ((sl2InverseTargetImage W T).filter (fun x =>
            P (MvPolynomial.eval x KW))).card := by
            simpa only [P, KW] using htransport.symm
      _ ≤ ((integerSymmetricRectangle A B).filter (fun x =>
            P (MvPolynomial.eval x KW))).card := Finset.card_le_card hsubset
      _ = (((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
            fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card := by
        simpa only [P, L₁, L₂, x0, y0, fxy, and_comm] using
          card_filter_integerSymmetricRectangle_eq_rangeProduct A B
            (fun x => P (MvPolynomial.eval x KW))
  have hfiltered :
      (((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
        MvPolynomial.eval y K ≠ 0).card : ℕ) : ℝ) ≤
      ((((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
        fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card : ℕ) := by
    exact_mod_cast hfilteredNat
  have hprod : (L₁ : ℝ) * (L₂ : ℝ) ≤ 144 * U * V / M := by
    rw [card_integerSymmetricRectangle] at harea
    simpa only [L₁, L₂, Nat.cast_mul] using harea
  have hL₁ : (L₁ : ℝ) ≤ 12 / mu := by
    rw [card_integerSymmetricInterval] at hsideA
    simpa only [L₁] using hsideA
  have hL₂raw : (L₂ : ℝ) ≤ 12 * mu / delta := by
    rw [card_integerSymmetricInterval] at hsideB
    simpa only [L₂] using hsideB
  have hBA : 12 * mu / delta ≤ 12 / mu := by
    apply (div_le_div_iff₀ hdelta hmu).mpr
    nlinarith
  have hL₂ : (L₂ : ℝ) ≤ 12 / mu := hL₂raw.trans hBA
  have hmax : ((max L₁ L₂ : ℕ) : ℝ) ≤ 12 / mu := by
    push_cast
    exact max_le hL₁ hL₂
  have hperimeter : (L₁ : ℝ) + (L₂ : ℝ) ≤ 24 / mu := by
    calc
      (L₁ : ℝ) + (L₂ : ℝ) ≤ 12 / mu + 12 / mu := add_le_add hL₁ hL₂
      _ = 24 / mu := by ring
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : 0 ≤ 1 + Real.log (16 * (N : ℝ) ^ 2) := by
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    have := Real.log_nonneg harg
    linarith
  have hcommon :
      (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
          Real.log (N : ℝ) / (N : ℝ) ≤
        (4608 / Real.log 2) * (U * V / M) *
          Real.log (N : ℝ) / (N : ℝ) := by
    have hscale : 0 ≤ (32 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ) := by
      positivity
    calc
      _ = ((32 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
          ((L₁ : ℝ) * (L₂ : ℝ)) := by ring
      _ ≤ ((32 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
          (144 * U * V / M) := mul_le_mul_of_nonneg_left hprod hscale
      _ = _ := by ring

  have hsieve' := hsieve Delta a Wval J j x0 y0 L₁ L₂ fxy rxy
    hDelta0 haDelta hDeltaHigher hWvalBudget hJhom hj hfactorEval hsize
  have hinner :
      16 * (N : ℝ) ^ 2 *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
          ((L₁ : ℝ) + (L₂ : ℝ)) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ≤
        16 * (N : ℝ) ^ 2 *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
          24 / mu * (1 + Real.log (16 * (N : ℝ) ^ 2)) := by
    exact add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_right hperimeter hLlog)
  have htrivialError :
      36 * (N : ℝ) *
          (16 * (N : ℝ) ^ 2 *
              (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
            ((L₁ : ℝ) + (L₂ : ℝ)) *
              (1 + Real.log (16 * (N : ℝ) ^ 2))) ≤
        576 * (N : ℝ) ^ 3 *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
          864 / mu * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) := by
    calc
      _ ≤ 36 * (N : ℝ) *
          (16 * (N : ℝ) ^ 2 *
              (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
            24 / mu *
              (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
        exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  calc
    (((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
        MvPolynomial.eval y K ≠ 0).card : ℕ) : ℝ) ≤
        ((((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
          fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card : ℕ) := hfiltered
    _ ≤ _ := hsieve'
    _ ≤ (4608 / Real.log 2) * (U * V / M) *
          Real.log (N : ℝ) / (N : ℝ) +
        (576 * (N : ℝ) ^ 3 *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
          864 / mu * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2))) :=
      add_le_add hcommon htrivialError
    _ = fullCellElementarySieveEnvelope N d U V M mu := by
      rw [fullCellElementarySieveEnvelope]
      ring

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
    obtain ⟨hWvalBudget, hcertBudget⟩ := hbudgets
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
      · simpa only [U, V] using hcertBudget
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

