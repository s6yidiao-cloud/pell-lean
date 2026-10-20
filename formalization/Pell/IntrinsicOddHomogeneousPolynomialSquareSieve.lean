import Pell.DyadicResidualFullCellSquareSieve
import Mathlib.Tactic

/-!
# Square sieve for an intrinsic odd homogeneous target polynomial

This module exposes the reusable core of the full-cell one-filter square
sieve.  The target polynomial and finite target set are arbitrary.  The
caller supplies a coefficient height for the polynomial after the selected
`SL₂(ℤ)` substitution, together with the same rectangle, value-height, and
resultant-certificate budgets used by the existing dyadic specialization.

The Weil estimate remains an explicit input.  No new character-sum theorem is
introduced here.
-/

namespace PellPaper

open Filter
open scoped MatrixGroups

noncomputable section

/-- An arbitrary odd-degree homogeneous integral polynomial has the same
one-filter full-cell square-sieve bound once its inverse `SL₂(ℤ)` target image,
transformed coefficient height, value height, and resultant certificate obey
the explicit budgets used by the dyadic argument.

The zero polynomial and empty target set need no separate hypotheses: their
nonzero-square filters are empty. -/
theorem eventually_fullCell_oddHomogeneousPolynomial_filter_le
    (hWeil : OneVariableQuadraticWeilDegreeBound) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (U V M mu delta A B : ℝ) (W : SL(2, ℤ))
        (T : Finset (Fin 2 → ℤ))
        (K : MvPolynomial (Fin 2) ℤ) (d HK : ℕ),
        0 < U → 0 < V → 0 < M → 0 < mu → 0 < delta →
        mu ^ 2 ≤ delta →
        K.IsHomogeneous d → Odd d → 0 < HK →
        (∀ e, |(binaryLinearSubstitution
          (W : Matrix (Fin 2) (Fin 2) ℤ) K).coeff e| ≤ (HK : ℤ)) →
        sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A B →
        ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M →
        ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu →
        ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta →
        A ≤ 4 * (U + V) → B ≤ 4 * (U + V) →
        let HJ : ℕ := 2 ^ d * (d + 1) * HK
        let Wval : ℝ :=
          ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
        Real.log Wval ≤ (Real.log 2 / 16) * (N : ℝ) →
        (∀ j : ℕ, Odd j → 0 < j → j ≤ d →
          fullCellCertificateLogMajorant d HK j +
              2 * Real.log (HJ : ℝ) ≤
            (Real.log 2 / 8) * (N : ℝ)) →
        (((T.filter fun y =>
          IsSquare (MvPolynomial.eval y K) ∧
            MvPolynomial.eval y K ≠ 0).card : ℝ)) ≤
          fullCellOddDegreeSieveEnvelope N d U V M mu := by
  filter_upwards
    [eventually_squareSieve_degreeOne_polynomial_rectangle_le,
      eventually_squareSieve_higherDegree_polynomial_rectangle_le_of_oneVariableQuadraticWeil
        hWeil,
      eventually_ge_atTop 4]
      with N hlinear hhigher hN
  intro U V M mu delta A B W T K d HK hU hV hM hmu hdelta hsq
    hKhom hdOdd hHK hKWcoeff hCsubset harea hsideA hsideB hcoordA hcoordB
  dsimp only
  intro hWvalBudget hcertBudget
  let KW : MvPolynomial (Fin 2) ℤ :=
    binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K
  let HJ : ℕ := 2 ^ d * (d + 1) * HK
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
  let x0 : ℤ := -⌊A⌋
  let y0 : ℤ := -⌊B⌋
  let L₁ : ℕ := (2 * ⌊A⌋ + 1).toNat
  let L₂ : ℕ := (2 * ⌊B⌋ + 1).toNat
  have hKWhom : KW.IsHomogeneous d :=
    binaryLinearSubstitution_isHomogeneous _ K d hKhom
  change ∀ e, |KW.coeff e| ≤ (HK : ℤ) at hKWcoeff
  have hHJ : 0 < HJ := by dsimp [HJ]; positivity
  have hEnvelope : 0 ≤ fullCellOddDegreeSieveEnvelope N d U V M mu := by
    have hNr : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N by omega)
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    have hLlog : 0 ≤ 1 + Real.log (16 * (N : ℝ) ^ 2) := by
      have := Real.log_nonneg harg
      linarith
    rw [fullCellOddDegreeSieveEnvelope]
    positivity
  change ((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
      MvPolynomial.eval y K ≠ 0).card : ℝ) ≤
    fullCellOddDegreeSieveEnvelope N d U V M mu
  by_cases hK0 : K = 0
  · simpa [hK0] using hEnvelope
  have hKW0 : KW ≠ 0 :=
    binaryLinearSubstitution_sl2_ne_zero W hK0
  obtain ⟨a, R, J, m, j, hfactor, ha, _hasq, _haHeight, hR0, hJ0,
      hRhom, hJhom, hdegree, hj, hjpos, _hprimitive, hJcoeff,
      hDelta0, hDeltaLog⟩ :=
    exists_homogeneous_square_factor_with_bounded_resultant_certificate
      KW d HK hKWhom hKW0 hdOdd hHK hKWcoeff
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
    exact Real.log_nonneg
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hHJ.ne'))
  have hDeltaHigher :
      Real.log (Delta.natAbs : ℝ) ≤
        (Real.log 2 / 8) * (N : ℝ) := by
    linarith
  have haDelta : a ∣ Delta := by
    refine ⟨2 * binaryProjectiveDerivativeResultant J j, ?_⟩
    dsimp [Delta]
    ring
  have hresultantDelta :
      binaryProjectiveDerivativeResultant J j ∣ Delta := by
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
    have hscale :
        0 ≤ (32 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ) := by
      positivity
    calc
      _ = ((32 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
          ((L₁ : ℝ) * (L₂ : ℝ)) := by ring
      _ ≤ ((32 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
          (144 * U * V / M) := mul_le_mul_of_nonneg_left hprod hscale
      _ = _ := by ring
  by_cases hj1 : j = 1
  · subst j
    have hsieve := hlinear Delta a HJ Wval J x0 y0 L₁ L₂ fxy rxy
      hDelta0 haDelta hJhom hJ0 hHJ hJcoeff hDeltaLinear hWvalBudget
      hfactorEval hsize
    have hlinearError :
        64 * ((max L₁ L₂ : ℕ) : ℝ) * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ≤
          768 / mu * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) := by
      have hscale : 0 ≤ 64 * (N : ℝ) *
          (1 + Real.log (16 * (N : ℝ) ^ 2)) := by positivity
      calc
        _ = (64 * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2))) *
              ((max L₁ L₂ : ℕ) : ℝ) := by ring
        _ ≤ (64 * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2))) * (12 / mu) :=
          mul_le_mul_of_nonneg_left hmax hscale
        _ = _ := by ring
    calc
      (((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
          MvPolynomial.eval y K ≠ 0).card : ℕ) : ℝ) ≤
          ((((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
            fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card : ℕ) := hfiltered
      _ ≤ _ := hsieve
      _ ≤ (4608 / Real.log 2) * (U * V / M) *
            Real.log (N : ℝ) / (N : ℝ) +
          768 / mu * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) :=
        add_le_add hcommon hlinearError
      _ ≤ fullCellOddDegreeSieveEnvelope N d U V M mu := by
        rw [fullCellOddDegreeSieveEnvelope]
        apply add_le_add (le_refl _)
        exact le_max_left _ _
  · have hj3 : 3 ≤ j := by
      obtain ⟨q, hq⟩ := hj
      omega
    have hsieve := hhigher Delta a Wval J j x0 y0 L₁ L₂ fxy rxy
      hDelta0 haDelta hresultantDelta hDeltaHigher hWvalBudget hJhom hj hj3
      hfactorEval hsize
    have hjd : (j : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hjle 1
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
    have hhigherError :
        4 * ((j : ℝ) + 1) ^ 2 *
            (16 * (N : ℝ) ^ 2 *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              ((L₁ : ℝ) + (L₂ : ℝ)) *
                (1 + Real.log (16 * (N : ℝ) ^ 2))) ≤
          4 * ((d : ℝ) + 1) ^ 2 *
            (16 * (N : ℝ) ^ 2 *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              24 / mu * (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
      gcongr
    calc
      (((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
          MvPolynomial.eval y K ≠ 0).card : ℕ) : ℝ) ≤
          ((((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
            fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card : ℕ) := hfiltered
      _ ≤ _ := hsieve
      _ ≤ (4608 / Real.log 2) * (U * V / M) *
            Real.log (N : ℝ) / (N : ℝ) +
          4 * ((d : ℝ) + 1) ^ 2 *
            (16 * (N : ℝ) ^ 2 *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              24 / mu * (1 + Real.log (16 * (N : ℝ) ^ 2))) :=
        add_le_add hcommon hhigherError
      _ ≤ fullCellOddDegreeSieveEnvelope N d U V M mu := by
        rw [fullCellOddDegreeSieveEnvelope]
        apply add_le_add (le_refl _)
        exact le_max_right _ _

end

end PellPaper
