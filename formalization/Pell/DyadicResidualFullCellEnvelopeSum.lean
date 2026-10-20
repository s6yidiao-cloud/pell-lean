import Pell.DyadicResidualFullCellSquareSieve
import Pell.DyadicSourceTargetCellPairs

/-!
# Summing the full-cell odd-degree square-sieve envelope

The local full-cell theorem returns a maximum of the sharp linear error and
the higher-degree Fourier error.  This file replaces that maximum by one
degree-monotone expression whose only centre-dependent term is the reciprocal
first minimum, and then sums it over the literal source/target cell-pair
cover.  The existing `1348 M` cell count and `21568` reciprocal-minimum sum
are used directly.

No curve-point count, auxiliary-form construction, sieve-scale choice, or
logarithmic budget discharge is asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A degree-monotone pointwise majorant for the local odd-degree envelope.
Its dependence on the target centre is exactly linear in `1 / mu`. -/
def fullCellOddDegreeSieveCommonEnvelope
    (N D : ℕ) (U V M mu : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  (4608 / Real.log 2) * (U * V / M) *
      Real.log (N : ℝ) / (N : ℝ) +
    64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2 +
    (768 * (N : ℝ) * Llog +
      96 * ((D : ℝ) + 1) ^ 2 * Llog) / mu

/-- The explicit result of summing the common envelope over every actual
source/target cell pair, using the proved cell-count and reciprocal-minimum
budgets. -/
def fullCellOddDegreeSieveAggregateEnvelope
    (N D : ℕ) (U V M : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * (U * V / M) *
        Real.log (N : ℝ) / (N : ℝ) +
      64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    768 * (N : ℝ) * Llog + 96 * ((D : ℝ) + 1) ^ 2 * Llog
  (1348 * M) * common + reciprocalCoefficient *
    (21568 * (Real.sqrt (U * V * M) + U + V) *
      (1 + Real.log (1 + U / Real.sqrt (U * V / M))))

/-- Positivity of the local envelope, exposed for enlarging a selected family
of full cells to the complete actual cell-pair cover. -/
theorem fullCellOddDegreeSieveEnvelope_nonnegative
    (N d : ℕ) (U V M mu : ℝ) (hN : 4 ≤ N)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hmu : 0 < mu) :
    0 ≤ fullCellOddDegreeSieveEnvelope N d U V M mu := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    nlinarith [sq_nonneg (N : ℝ)]
  have hLlog : 0 ≤ 1 + Real.log (16 * (N : ℝ) ^ 2) := by
    linarith [Real.log_nonneg harg]
  rw [fullCellOddDegreeSieveEnvelope]
  positivity

/-- For `N ≥ 4`, increasing the public degree bound replaces the branch
maximum by the common envelope. -/
theorem fullCellOddDegreeSieveEnvelope_le_common
    (N d D : ℕ) (U V M mu : ℝ)
    (hN : 4 ≤ N) (hd : d ≤ D) (hmu : 0 < mu) :
    fullCellOddDegreeSieveEnvelope N d U V M mu ≤
      fullCellOddDegreeSieveCommonEnvelope N D U V M mu := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hLlog : 0 ≤ 1 + Real.log (16 * (N : ℝ) ^ 2) := by
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hdR : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd
  have hdSq : ((d : ℝ) + 1) ^ 2 ≤ ((D : ℝ) + 1) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ D by positivity]
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  have hLlog' : 0 ≤ Llog := by simpa [Llog] using hLlog
  let degreeError : ℝ :=
    64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalError : ℝ :=
    (768 * (N : ℝ) * Llog +
      96 * ((D : ℝ) + 1) ^ 2 * Llog) / mu
  have hdegreeError : 0 ≤ degreeError := by
    dsimp [degreeError]
    positivity
  have hlinear :
      768 / mu * (N : ℝ) * Llog ≤ degreeError + reciprocalError := by
    have hrecip :
        768 / mu * (N : ℝ) * Llog ≤ reciprocalError := by
      dsimp [reciprocalError]
      rw [show 768 / mu * (N : ℝ) * Llog =
        (768 * (N : ℝ) * Llog) / mu by ring]
      apply div_le_div_of_nonneg_right
      have hDterm : 0 ≤ 96 * ((D : ℝ) + 1) ^ 2 * Llog := by positivity
      nlinarith
      exact hmu.le
    linarith
  have hhigher :
      4 * ((d : ℝ) + 1) ^ 2 *
          (16 * (N : ℝ) ^ 2 * Llog ^ 2 + 24 / mu * Llog) ≤
        degreeError + reciprocalError := by
    have hdegPart :
        64 * ((d : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2 ≤
          degreeError := by
      dsimp [degreeError]
      gcongr
    have hrecipPart :
        (96 * ((d : ℝ) + 1) ^ 2 * Llog) / mu ≤ reciprocalError := by
      dsimp [reciprocalError]
      apply div_le_div_of_nonneg_right
      have hNterm : 0 ≤ 768 * (N : ℝ) * Llog := by positivity
      have hdegreeTerm :
          96 * ((d : ℝ) + 1) ^ 2 * Llog ≤
            96 * ((D : ℝ) + 1) ^ 2 * Llog := by
        gcongr
      linarith
      exact hmu.le
    calc
      4 * ((d : ℝ) + 1) ^ 2 *
          (16 * (N : ℝ) ^ 2 * Llog ^ 2 + 24 / mu * Llog) =
          64 * ((d : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2 +
            (96 * ((d : ℝ) + 1) ^ 2 * Llog) / mu := by ring
      _ ≤ degreeError + reciprocalError := add_le_add hdegPart hrecipPart
  rw [fullCellOddDegreeSieveEnvelope,
    fullCellOddDegreeSieveCommonEnvelope]
  change _ + max
      (768 / mu * (N : ℝ) * Llog)
      (4 * ((d : ℝ) + 1) ^ 2 *
        (16 * (N : ℝ) ^ 2 * Llog ^ 2 + 24 / mu * Llog)) ≤
    _ + degreeError + reciprocalError
  linarith [max_le hlinear hhigher]

/-- The total local envelope over the complete literal cell-pair cover is
bounded by the explicit aggregate envelope.  The degree may vary from cell
to cell, but must lie below the common bound `D`. -/
theorem sum_fullCellOddDegreeSieveEnvelope_dyadicSourceTargetCellPairs_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M N D : ℕ}
    (hM : 0 < M)
    (hscale : (M : ℝ) ≤
      ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hN : 4 ≤ N) (degree : ℕ × ℤ → ℕ)
    (hdegree : ∀ p ∈ dyadicSourceTargetCellPairs theta Y i M,
      degree p ≤ D) :
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    (∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
      fullCellOddDegreeSieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
      fullCellOddDegreeSieveAggregateEnvelope N D U V (M : ℝ) := by
  dsimp only
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let P : Finset (ℕ × ℤ) := dyadicSourceTargetCellPairs theta Y i M
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * (U * V / (M : ℝ)) *
        Real.log (N : ℝ) / (N : ℝ) +
      64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    768 * (N : ℝ) * Llog + 96 * ((D : ℝ) + 1) ^ 2 * Llog
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : 0 ≤ Llog := by
    dsimp [Llog]
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hcommon : 0 ≤ common := by
    dsimp [common]
    positivity
  have hcoefficient : 0 ≤ reciprocalCoefficient := by
    dsimp [reciprocalCoefficient]
    positivity
  have hpointwise :
      (∑ p ∈ P,
        fullCellOddDegreeSieveEnvelope N (degree p) U V (M : ℝ)
          (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        ∑ p ∈ P,
          fullCellOddDegreeSieveCommonEnvelope N D U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    apply fullCellOddDegreeSieveEnvelope_le_common N (degree p) D
      U V (M : ℝ) _ hN
    · exact hdegree p hp
    · exact firstSlopeSupNorm_pos U V (M : ℝ) (p.2 : ℝ) hU hV hMr
  have hrewrite :
      (∑ p ∈ P,
        fullCellOddDegreeSieveCommonEnvelope N D U V (M : ℝ)
          (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) =
        (P.card : ℝ) * common + reciprocalCoefficient *
          ∑ p ∈ P, reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ) := by
    calc
      (∑ p ∈ P,
        fullCellOddDegreeSieveCommonEnvelope N D U V (M : ℝ)
          (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) =
          ∑ p ∈ P, (common + reciprocalCoefficient *
            reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [fullCellOddDegreeSieveCommonEnvelope,
          reciprocalFirstSlopeSupNorm, Llog, common, reciprocalCoefficient]
        ring
      _ = (∑ _p ∈ P, common) +
          ∑ p ∈ P, reciprocalCoefficient *
            reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ) := by
        rw [Finset.sum_add_distrib]
      _ = (P.card : ℝ) * common + reciprocalCoefficient *
          ∑ p ∈ P,
            reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hcardNat := card_dyadicSourceTargetCellPairs_le
    theta Y i hM hscale
  have hcard : (P.card : ℝ) ≤ 1348 * (M : ℝ) := by
    dsimp [P]
    exact_mod_cast hcardNat
  have hsum :=
    sum_reciprocalFirstSlopeSupNorm_dyadicSourceTargetCellPairs_le
      theta Y i hM hscale
  have hcardTerm : (P.card : ℝ) * common ≤
      (1348 * (M : ℝ)) * common :=
    mul_le_mul_of_nonneg_right hcard hcommon
  have hrecipTerm :
      reciprocalCoefficient *
          (∑ p ∈ P,
            reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) ≤
        reciprocalCoefficient *
          (21568 * (Real.sqrt (U * V * (M : ℝ)) + U + V) *
            (1 + Real.log
              (1 + U / Real.sqrt (U * V / (M : ℝ))))) := by
    apply mul_le_mul_of_nonneg_left
    · simpa only [P, U, V] using hsum
    · exact hcoefficient
  calc
    (∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
      fullCellOddDegreeSieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        ∑ p ∈ P,
          fullCellOddDegreeSieveCommonEnvelope N D U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
      simpa only [P] using hpointwise
    _ = (P.card : ℝ) * common + reciprocalCoefficient *
          ∑ p ∈ P,
            reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ) := hrewrite
    _ ≤ (1348 * (M : ℝ)) * common + reciprocalCoefficient *
          (21568 * (Real.sqrt (U * V * (M : ℝ)) + U + V) *
            (1 + Real.log
              (1 + U / Real.sqrt (U * V / (M : ℝ))))) :=
      add_le_add hcardTerm hrecipTerm
    _ = fullCellOddDegreeSieveAggregateEnvelope N D U V (M : ℝ) := by
      simp only [fullCellOddDegreeSieveAggregateEnvelope, Llog, common,
        reciprocalCoefficient]

/-- The same aggregate controls any selected subfamily of actual cell pairs.
This is the form used after separating strict-thin from full cells. -/
theorem sum_fullCellOddDegreeSieveEnvelope_subset_dyadicSourceTargetCellPairs_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M N D : ℕ}
    (hM : 0 < M)
    (hscale : (M : ℝ) ≤
      ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hN : 4 ≤ N) (I : Finset (ℕ × ℤ))
    (hI : I ⊆ dyadicSourceTargetCellPairs theta Y i M)
    (degree : ℕ × ℤ → ℕ)
    (hdegree : ∀ p ∈ dyadicSourceTargetCellPairs theta Y i M,
      degree p ≤ D) :
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    (∑ p ∈ I,
      fullCellOddDegreeSieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
      fullCellOddDegreeSieveAggregateEnvelope N D U V (M : ℝ) := by
  dsimp only
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    (∑ p ∈ I,
      fullCellOddDegreeSieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        ∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
          fullCellOddDegreeSieveEnvelope N (degree p) U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hI
      intro p _ _
      apply fullCellOddDegreeSieveEnvelope_nonnegative N (degree p)
        U V (M : ℝ) _ hN hU hV hMr
      exact firstSlopeSupNorm_pos U V (M : ℝ) (p.2 : ℝ) hU hV hMr
    _ ≤ fullCellOddDegreeSieveAggregateEnvelope N D U V (M : ℝ) := by
      exact sum_fullCellOddDegreeSieveEnvelope_dyadicSourceTargetCellPairs_le
        theta Y i hM hscale hN degree hdegree

end

end PellPaper
