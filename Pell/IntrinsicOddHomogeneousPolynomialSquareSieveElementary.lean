import Pell.AnisotropicSharpSquareSieve
import Pell.DyadicResidualFullCellSquareSieve
import Pell.FullCellElementarySieveEnvelope
import Mathlib.Tactic

/-!
# The manuscript square sieve in reduced lattice coordinates

The parameterized rectangle estimate applies directly to an arbitrary odd
homogeneous form. Reduced coordinates supply the area, perimeter and value
height bounds; no factorization or bad-prime certificate is needed.
-/

namespace PellPaper

open Filter
open scoped MatrixGroups

noncomputable section

/-- An arbitrary odd homogeneous polynomial satisfies the full-cell envelope
from the manuscript's parameterized square sieve. The value-height condition
is the only arithmetic budget; the remaining assumptions describe the
reduced rectangle and its polynomial coefficients. -/
theorem eventually_fullCell_oddHomogeneousPolynomial_filter_le_elementary :
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
        let Wval : ℝ :=
          ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
        Real.log Wval ≤ (Real.log 2 / 16) * (N : ℝ) →
        (((T.filter fun y =>
          IsSquare (MvPolynomial.eval y K) ∧
            MvPolynomial.eval y K ≠ 0).card : ℝ)) ≤
          fullCellElementarySieveEnvelope N d U V M mu := by
  filter_upwards
    [eventually_oddHomogeneous_rectangle_squareSieve,
      eventually_ge_atTop 4]
      with N hrectangle hN
  intro U V M mu delta A B W T K d HK hU hV hM hmu hdelta hsq
    hKhom hdOdd hHK hKWcoeff hCsubset harea hsideA hsideB hcoordA hcoordB
  dsimp only
  intro hWvalBudget
  let KW : MvPolynomial (Fin 2) ℤ :=
    binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
  let x0 : ℤ := -⌊A⌋
  let y0 : ℤ := -⌊B⌋
  let L₁ : ℕ := (2 * ⌊A⌋ + 1).toNat
  let L₂ : ℕ := (2 * ⌊B⌋ + 1).toNat
  have hKWhom : KW.IsHomogeneous d :=
    binaryLinearSubstitution_isHomogeneous _ K d hKhom
  change ∀ e, |KW.coeff e| ≤ (HK : ℤ) at hKWcoeff
  let fxy : ℕ × ℕ → ℤ := fun xy =>
    MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] KW
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
    linarith [Real.log_nonneg harg]
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
  have hsieve := hrectangle Wval KW d x0 y0 L₁ L₂
    hWvalBudget hKWhom hdOdd hsize
  have hperimeterTerm :
      36 * (N : ℝ) *
          (((L₁ : ℝ) + (L₂ : ℝ)) *
            (1 + Real.log (16 * (N : ℝ) ^ 2))) ≤
        864 * (N : ℝ) *
          (1 + Real.log (16 * (N : ℝ) ^ 2)) / mu := by
    calc
      _ ≤ 36 * (N : ℝ) *
          ((24 / mu) * (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
        gcongr
      _ = _ := by ring
  calc
    (((T.filter fun y => IsSquare (MvPolynomial.eval y K) ∧
        MvPolynomial.eval y K ≠ 0).card : ℕ) : ℝ) ≤
        ((((Finset.range L₁).product (Finset.range L₂)).filter fun xy =>
          fxy xy ≠ 0 ∧ IsSquare (fxy xy)).card : ℕ) := hfiltered
    _ ≤ _ := hsieve
    _ ≤ (4608 / Real.log 2) * (U * V / M) *
          Real.log (N : ℝ) / (N : ℝ) +
        576 * (N : ℝ) ^ 3 *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
        864 * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) / mu := by
      calc
        _ ≤ (4608 / Real.log 2) * (U * V / M) *
              Real.log (N : ℝ) / (N : ℝ) +
            36 * (N : ℝ) *
              ((16 * (N : ℝ) ^ 2) *
                  (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
                ((L₁ : ℝ) + (L₂ : ℝ)) *
                  (1 + Real.log (16 * (N : ℝ) ^ 2))) :=
          add_le_add hcommon (le_refl _)
        _ ≤ _ := by
          have hbulk :
              36 * (N : ℝ) *
                  ((16 * (N : ℝ) ^ 2) *
                    (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2) =
                576 * (N : ℝ) ^ 3 *
                  (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 := by ring
          rw [mul_add, hbulk]
          linarith
    _ = fullCellElementarySieveEnvelope N d U V M mu := by
      rfl

end

end PellPaper

