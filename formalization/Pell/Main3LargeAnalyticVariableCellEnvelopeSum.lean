import Pell.DyadicResidualFullCellEnvelopeSum
import Mathlib.Tactic

/-!
# Summing square-sieve envelopes with variable cell geometry

The odd-degree sieve envelope has a cell-independent part, an area term, and
a term linear in the reciprocal first minimum.  This module isolates the
finite-sum bookkeeping needed when the geometric parameters vary from cell
to cell.  The caller supplies only uniform degree and area bounds, a cell
count bound, and one bound for the reciprocal-minimum sum.

No character-sum or Main3-specific geometric input occurs here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The common finite-family envelope after replacing the number of cells,
the area term, and the reciprocal-minimum sum by supplied upper bounds. -/
def fullCellOddDegreeSieveVariableAggregateEnvelope
    (N D : ℕ) (cellCount area reciprocalSum : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * area * Real.log (N : ℝ) / (N : ℝ) +
      64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    768 * (N : ℝ) * Llog +
      96 * ((D : ℝ) + 1) ^ 2 * Llog
  cellCount * common + reciprocalCoefficient * reciprocalSum

/-- The sharper aggregate in which the caller supplies the sum of the actual
cell area terms, rather than a pointwise area bound times a cell count. -/
def fullCellOddDegreeSieveAreaReciprocalAggregateEnvelope
    (N D : ℕ) (cellCount areaSum reciprocalSum : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let areaCoefficient : ℝ :=
    (4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)
  let degreeTerm : ℝ :=
    64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    768 * (N : ℝ) * Llog +
      96 * ((D : ℝ) + 1) ^ 2 * Llog
  areaCoefficient * areaSum + cellCount * degreeTerm +
    reciprocalCoefficient * reciprocalSum

/-- Sum the common envelope using a bound for the total area contribution
and a bound for the total reciprocal first minimum. -/
theorem sum_fullCellOddDegreeSieveEnvelope_le_of_area_reciprocal_budgets
    {ι : Type*} (J : Finset ι) (N D : ℕ)
    (degree : ι → ℕ) (U V M mu : ι → ℝ)
    (areaSum reciprocalSum : ℝ)
    (hN : 4 ≤ N)
    (hdegree : ∀ i ∈ J, degree i ≤ D)
    (hmu : ∀ i ∈ J, 0 < mu i)
    (hareaSum :
      (∑ i ∈ J, U i * V i / M i) ≤ areaSum)
    (hreciprocal :
      (∑ i ∈ J, 1 / mu i) ≤ reciprocalSum) :
    (∑ i ∈ J,
      fullCellOddDegreeSieveEnvelope N (degree i) (U i) (V i) (M i)
        (mu i)) ≤
      fullCellOddDegreeSieveAreaReciprocalAggregateEnvelope
        N D (J.card : ℝ) areaSum reciprocalSum := by
  classical
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let areaCoefficient : ℝ :=
    (4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)
  let degreeTerm : ℝ :=
    64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    768 * (N : ℝ) * Llog +
      96 * ((D : ℝ) + 1) ^ 2 * Llog
  have hNr : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : 0 ≤ Llog := by
    dsimp [Llog]
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hareaCoefficient : 0 ≤ areaCoefficient := by
    dsimp [areaCoefficient]
    positivity
  have hreciprocalCoefficient : 0 ≤ reciprocalCoefficient := by
    dsimp [reciprocalCoefficient]
    positivity
  have hpointwise : ∀ i ∈ J,
      fullCellOddDegreeSieveEnvelope N (degree i) (U i) (V i) (M i)
          (mu i) ≤
        areaCoefficient * (U i * V i / M i) + degreeTerm +
          reciprocalCoefficient / mu i := by
    intro i hi
    have henvelope := fullCellOddDegreeSieveEnvelope_le_common
      N (degree i) D (U i) (V i) (M i) (mu i)
        hN (hdegree i hi) (hmu i hi)
    apply henvelope.trans
    rw [fullCellOddDegreeSieveCommonEnvelope]
    dsimp [areaCoefficient, degreeTerm, reciprocalCoefficient, Llog]
    ring_nf
    exact le_rfl
  calc
    (∑ i ∈ J,
        fullCellOddDegreeSieveEnvelope N (degree i) (U i) (V i) (M i)
          (mu i)) ≤
        ∑ i ∈ J,
          (areaCoefficient * (U i * V i / M i) + degreeTerm +
            reciprocalCoefficient / mu i) :=
      Finset.sum_le_sum hpointwise
    _ = areaCoefficient * (∑ i ∈ J, U i * V i / M i) +
          (J.card : ℝ) * degreeTerm +
          reciprocalCoefficient * (∑ i ∈ J, 1 / mu i) := by
      simp_rw [show ∀ i, reciprocalCoefficient / mu i =
          reciprocalCoefficient * (1 / mu i) by
        intro i
        ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ areaCoefficient * areaSum + (J.card : ℝ) * degreeTerm +
          reciprocalCoefficient * reciprocalSum := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hareaSum hareaCoefficient)
          (le_refl _))
        (mul_le_mul_of_nonneg_left hreciprocal
          hreciprocalCoefficient)
    _ = fullCellOddDegreeSieveAreaReciprocalAggregateEnvelope
          N D (J.card : ℝ) areaSum reciprocalSum := by
      rfl

/-- A finite family of odd-degree sieve envelopes is controlled by uniform
degree and area bounds together with the actual reciprocal-minimum sum.  All
cell parameters may vary independently. -/
theorem sum_fullCellOddDegreeSieveEnvelope_le_variableAggregate
    {ι : Type*} (J : Finset ι) (N D : ℕ)
    (degree : ι → ℕ) (U V M mu : ι → ℝ)
    (cellCount area reciprocalSum : ℝ)
    (hN : 4 ≤ N)
    (hdegree : ∀ i ∈ J, degree i ≤ D)
    (hmu : ∀ i ∈ J, 0 < mu i)
    (hcellCount : (J.card : ℝ) ≤ cellCount)
    (harea : 0 ≤ area)
    (hareaBound : ∀ i ∈ J, U i * V i / M i ≤ area)
    (hreciprocal :
      (∑ i ∈ J, 1 / mu i) ≤ reciprocalSum) :
    (∑ i ∈ J,
      fullCellOddDegreeSieveEnvelope N (degree i) (U i) (V i) (M i)
        (mu i)) ≤
      fullCellOddDegreeSieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum := by
  classical
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let common : ℝ :=
    (4608 / Real.log 2) * area * Real.log (N : ℝ) / (N : ℝ) +
      64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2
  let reciprocalCoefficient : ℝ :=
    768 * (N : ℝ) * Llog +
      96 * ((D : ℝ) + 1) ^ 2 * Llog
  have hNr : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : 0 ≤ Llog := by
    dsimp [Llog]
    have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [Real.log_nonneg harg]
  have hareaCoefficient :
      0 ≤ (4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ) := by
    positivity
  have hcommon : 0 ≤ common := by
    dsimp [common]
    have hareaTerm :
        0 ≤ (4608 / Real.log 2) * area *
          Real.log (N : ℝ) / (N : ℝ) := by
      positivity
    have hdegreeTerm :
        0 ≤ 64 * ((D : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 * Llog ^ 2 := by
      positivity
    linarith
  have hreciprocalCoefficient : 0 ≤ reciprocalCoefficient := by
    dsimp [reciprocalCoefficient]
    positivity
  have hpointwise : ∀ i ∈ J,
      fullCellOddDegreeSieveEnvelope N (degree i) (U i) (V i) (M i)
          (mu i) ≤
        common + reciprocalCoefficient / mu i := by
    intro i hi
    have henvelope := fullCellOddDegreeSieveEnvelope_le_common
      N (degree i) D (U i) (V i) (M i) (mu i)
        hN (hdegree i hi) (hmu i hi)
    have hareaTerm :
        (4608 / Real.log 2) * (U i * V i / M i) *
              Real.log (N : ℝ) / (N : ℝ) ≤
          (4608 / Real.log 2) * area *
              Real.log (N : ℝ) / (N : ℝ) := by
      calc
        (4608 / Real.log 2) * (U i * V i / M i) *
              Real.log (N : ℝ) / (N : ℝ) =
            ((4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
              (U i * V i / M i) := by ring
        _ ≤ ((4608 / Real.log 2) * Real.log (N : ℝ) / (N : ℝ)) *
              area :=
          mul_le_mul_of_nonneg_left (hareaBound i hi) hareaCoefficient
        _ = (4608 / Real.log 2) * area *
              Real.log (N : ℝ) / (N : ℝ) := by ring
    apply henvelope.trans
    rw [fullCellOddDegreeSieveCommonEnvelope]
    dsimp [common, reciprocalCoefficient, Llog]
    linarith
  calc
    (∑ i ∈ J,
        fullCellOddDegreeSieveEnvelope N (degree i) (U i) (V i) (M i)
          (mu i)) ≤
        ∑ i ∈ J, (common + reciprocalCoefficient / mu i) :=
      Finset.sum_le_sum hpointwise
    _ = (J.card : ℝ) * common +
        reciprocalCoefficient * (∑ i ∈ J, 1 / mu i) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ cellCount * common + reciprocalCoefficient * reciprocalSum := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcellCount hcommon)
        (mul_le_mul_of_nonneg_left hreciprocal hreciprocalCoefficient)
    _ = fullCellOddDegreeSieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum := by
      rfl

end

end PellPaper
