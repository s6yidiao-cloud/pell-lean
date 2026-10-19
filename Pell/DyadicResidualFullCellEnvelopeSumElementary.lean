import Pell.DyadicResidualFullCellSquareSieveElementary
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
def fullCellElementarySieveCommonEnvelope
    (N _D : ℕ) (U V M mu : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  (4608 / Real.log 2) * (U * V / M) *
      Real.log (N : ℝ) / (N : ℝ) +
    576 * (N : ℝ) ^ 3 * Llog ^ 2 +
    864 * (N : ℝ) * Llog / mu

/-- The explicit result of summing the common envelope over every actual
source/target cell pair, using the proved cell-count and reciprocal-minimum
budgets. -/
def fullCellElementarySieveAggregateEnvelope
    (N _D : ℕ) (U V M : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * (U * V / M) *
        Real.log (N : ℝ) / (N : ℝ) +
      576 * (N : ℝ) ^ 3 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    864 * (N : ℝ) * Llog
  (1348 * M) * common + reciprocalCoefficient *
    (21568 * (Real.sqrt (U * V * M) + U + V) *
      (1 + Real.log (1 + U / Real.sqrt (U * V / M))))

/-- Positivity of the local envelope, exposed for enlarging a selected family
of full cells to the complete actual cell-pair cover. -/
theorem fullCellElementarySieveEnvelope_nonnegative_aggregate
    (N d : ℕ) (U V M mu : ℝ) (hN : 4 ≤ N)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hmu : 0 < mu) :
    0 ≤ fullCellElementarySieveEnvelope N d U V M mu := by
  exact fullCellElementarySieveEnvelope_nonnegative
    N d U V M mu hN hU hV hM hmu

/-- For `N ≥ 4`, increasing the public degree bound replaces the branch
maximum by the common envelope. -/
theorem fullCellElementarySieveEnvelope_le_common
    (N d D : ℕ) (U V M mu : ℝ)
    (_hN : 4 ≤ N) (_hd : d ≤ D) (_hmu : 0 < mu) :
    fullCellElementarySieveEnvelope N d U V M mu ≤
      fullCellElementarySieveCommonEnvelope N D U V M mu := by
  simp only [fullCellElementarySieveEnvelope,
    fullCellElementarySieveCommonEnvelope]
  exact le_rfl

/-- The total local envelope over the complete literal cell-pair cover is
bounded by the explicit aggregate envelope.  The degree may vary from cell
to cell, but must lie below the common bound `D`. -/
theorem sum_fullCellElementarySieveEnvelope_dyadicSourceTargetCellPairs_le
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
      fullCellElementarySieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
      fullCellElementarySieveAggregateEnvelope N D U V (M : ℝ) := by
  dsimp only
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let P : Finset (ℕ × ℤ) := dyadicSourceTargetCellPairs theta Y i M
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * (U * V / (M : ℝ)) *
        Real.log (N : ℝ) / (N : ℝ) +
      576 * (N : ℝ) ^ 3 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    864 * (N : ℝ) * Llog
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
        fullCellElementarySieveEnvelope N (degree p) U V (M : ℝ)
          (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        ∑ p ∈ P,
          fullCellElementarySieveCommonEnvelope N D U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    apply fullCellElementarySieveEnvelope_le_common N (degree p) D
      U V (M : ℝ) _ hN
    · exact hdegree p hp
    · exact firstSlopeSupNorm_pos U V (M : ℝ) (p.2 : ℝ) hU hV hMr
  have hrewrite :
      (∑ p ∈ P,
        fullCellElementarySieveCommonEnvelope N D U V (M : ℝ)
          (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) =
        (P.card : ℝ) * common + reciprocalCoefficient *
          ∑ p ∈ P, reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ) := by
    calc
      (∑ p ∈ P,
        fullCellElementarySieveCommonEnvelope N D U V (M : ℝ)
          (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) =
          ∑ p ∈ P, (common + reciprocalCoefficient *
            reciprocalFirstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [fullCellElementarySieveCommonEnvelope,
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
      fullCellElementarySieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        ∑ p ∈ P,
          fullCellElementarySieveCommonEnvelope N D U V (M : ℝ)
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
    _ = fullCellElementarySieveAggregateEnvelope N D U V (M : ℝ) := by
      simp only [fullCellElementarySieveAggregateEnvelope, Llog, common,
        reciprocalCoefficient]

/-- The same aggregate controls any selected subfamily of actual cell pairs.
This is the form used after separating strict-thin from full cells. -/
theorem sum_fullCellElementarySieveEnvelope_subset_dyadicSourceTargetCellPairs_le
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
      fullCellElementarySieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
      fullCellElementarySieveAggregateEnvelope N D U V (M : ℝ) := by
  dsimp only
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    (∑ p ∈ I,
      fullCellElementarySieveEnvelope N (degree p) U V (M : ℝ)
        (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        ∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
          fullCellElementarySieveEnvelope N (degree p) U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hI
      intro p _ _
      apply fullCellElementarySieveEnvelope_nonnegative_aggregate N (degree p)
        U V (M : ℝ) _ hN hU hV hMr
      exact firstSlopeSupNorm_pos U V (M : ℝ) (p.2 : ℝ) hU hV hMr
    _ ≤ fullCellElementarySieveAggregateEnvelope N D U V (M : ℝ) := by
      exact sum_fullCellElementarySieveEnvelope_dyadicSourceTargetCellPairs_le
        theta Y i hM hscale hN degree hdegree

end

end PellPaper
