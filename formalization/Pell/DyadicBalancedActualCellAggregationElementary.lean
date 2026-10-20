import Pell.DyadicResidualFullCellEnvelopeSumElementary
import Pell.DyadicResidualFullCellCountElementary
import Pell.DyadicThinResidualSquareCount
import Pell.DyadicSourceTargetTupleCellCover
import Pell.FiniteCellSparsity

/-!
# Conditional thin/full aggregation over actual dyadic tuple cells

This draft combines the literal source-target tuple-cell cover with the
accepted thin and full source-tuple counts.  Auxiliary forms and their heights
may vary from cell to cell.  The only analytic black box is the explicit
one-variable quadratic Weil hypothesis already used by the local full-cell
count.

The result remains conditional on the local auxiliary forms and full-cell
sieve budgets; choosing the determinant and sieve parameters is a later
project-specific step.  No tuple/image cardinality identity is used.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- The local full-cell envelope is monotone in its public degree parameter.
The hypotheses make every degree-dependent multiplier nonnegative. -/
theorem fullCellElementarySieveEnvelope_mono_degree
    {N d D : ℕ} {U V M mu : ℝ} (_hN : 4 ≤ N) (_hmu : 0 < mu)
    (_hd : d ≤ D) :
    fullCellElementarySieveEnvelope N d U V M mu ≤
      fullCellElementarySieveEnvelope N D U V M mu := by
  simp only [fullCellElementarySieveEnvelope]
  exact le_rfl

/-- **Actual-cell thin/full aggregation.**  Once every heavy actual tuple
cell has its own bounded degree-`n` auxiliary form, and the logarithmic
budgets are available whenever that cell lies in the full branch, the whole
dyadic factor-box cell satisfies the displayed explicit bound.

The eventual square-sieve threshold is uniform: `N` is chosen before every
degree, dyadic box, cellwise form, and coefficient height. -/
theorem eventually_dyadicFactorBoxCell_card_le_thinFull_of_cellwiseAuxiliary_elementary :
    ∀ᶠ N : ℕ in atTop,
      ∀ (n H0 : ℕ) (theta Q : ℝ) (Y : ℕ)
        (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ),
        0 < M → 2 ≤ Y → 2 ≤ Q →
        (M : ℝ) ≤
          ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (2 * Q) →
        let P := dyadicSourceTargetCellPairs theta Y i M
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        let cell : ℕ × ℤ → Finset (ℕ × ℕ × ℕ × ℕ) :=
          fun p => dyadicSourceTargetTupleCell theta Y i M p.1 p.2
        (∀ p ∈ P, H0 ≤ (cell p).card →
          ∃ (f : twoLayerFormIndex n → ℤ) (H : ℝ),
            f ≠ 0 ∧ 0 ≤ H ∧
            (∀ ab, |((f ab : ℤ) : ℝ)| ≤ H) ∧
            (∀ q ∈ cell p, twoLayerFormEval n f
              (((q.1 : ℤ), (q.2.1 : ℤ)),
                ((q.2.2.2 : ℤ), (q.2.2.1 : ℤ))) = 0) ∧
            (1 ≤ 4 * firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ) /
                ((M : ℝ) / (U * V)) →
              ∀ b ≤ n, fullCellResidualSieveBudgets N i M b
                (positiveNatCeil
                  ((2 : ℝ) ^ n * ((n : ℝ) + 1) * H)))) →
        ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * Q * (n : ℝ) + 16) +
            8 * fullCellElementarySieveAggregateEnvelope
              N (2 * n + 1) U V (M : ℝ) := by
  filter_upwards
    [eventually_exists_bounded_twoLayer_common_factor_with_full_dyadic_count_elementary, eventually_ge_atTop 4] with N hfull hN
  intro n H0 theta Q Y i M hM hY hQ hscale hxQ
  dsimp only
  let P : Finset (ℕ × ℤ) := dyadicSourceTargetCellPairs theta Y i M
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let cell : ℕ × ℤ → Finset (ℕ × ℕ × ℕ × ℕ) :=
    fun p => dyadicSourceTargetTupleCell theta Y i M p.1 p.2
  let I : Finset (ℕ × ℤ) := P.filter fun p => H0 ≤ (cell p).card
  let cellBase : ℝ := 96 * Q * (n : ℝ) + 16
  intro haux
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hQr : 0 ≤ Q := le_trans (by norm_num) hQ
  have hbase : 0 ≤ cellBase := by
    dsimp [cellBase]
    positivity
  have hH0r : (0 : ℝ) ≤ H0 := by positivity
  have hIP : I ⊆ P := Finset.filter_subset _ _
  have hcover :
      dyadicFactorBoxCell theta Y i ⊆ finiteCellUnion P cell := by
    simpa only [finiteCellUnion, P, cell] using
      dyadicFactorBoxCell_subset_biUnion_sourceTargetTupleCells
        theta Y i hM
  have hsparseNat :
      (dyadicFactorBoxCell theta Y i).card ≤
        P.card * H0 + (heavyCellUnion P cell H0).card :=
    card_le_cellCount_mul_threshold_add_heavyCellUnion_of_subset hcover
  have hsparse :
      ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
        (P.card : ℝ) * (H0 : ℝ) +
          ((heavyCellUnion P cell H0).card : ℝ) := by
    exact_mod_cast hsparseNat
  have hheavySubset :
      heavyCellUnion P cell H0 ⊆ I.biUnion cell := by
    intro q hq
    obtain ⟨p, hp, hheavy, hqcell⟩ := mem_heavyCellUnion_iff.mp hq
    apply Finset.mem_biUnion.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hheavy⟩, hqcell⟩
  have hheavyNat :
      (heavyCellUnion P cell H0).card ≤
        ∑ p ∈ I, (cell p).card :=
    (Finset.card_le_card hheavySubset).trans Finset.card_biUnion_le
  have hheavy :
      ((heavyCellUnion P cell H0).card : ℝ) ≤
        ∑ p ∈ I, ((cell p).card : ℝ) := by
    exact_mod_cast hheavyNat
  have hpointwise : ∀ p ∈ I,
      ((cell p).card : ℝ) ≤ cellBase +
        8 * fullCellElementarySieveEnvelope N (2 * n + 1)
          U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
    intro p hpI
    have hpP : p ∈ P := hIP hpI
    have hoccupancy : H0 ≤ (cell p).card := (Finset.mem_filter.mp hpI).2
    obtain ⟨f, H, hf0, hH, hf, hzero, hbudgets⟩ :=
      haux p hpP hoccupancy
    have hk : p.2 ∈ targetSlopeIntegerCenters (M : ℝ) := by
      exact ((mem_dyadicSourceTargetCellPairs theta Y i M p.1 p.2).mp
        (by simpa only [P] using hpP)).2
    let mu : ℝ := firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)
    let delta : ℝ := (M : ℝ) / (U * V)
    have hmu : 0 < mu := by
      dsimp [mu]
      exact firstSlopeSupNorm_pos U V (M : ℝ) (p.2 : ℝ) hU hV hMr
    by_cases hthin : 4 * mu / delta < 1
    · obtain ⟨d, b, D, f', hdb, hD0, hDhom, hf'0, hfactor, hHD,
          hHf', hcomponents, heval, hz, hcount⟩ :=
        exists_bounded_twoLayer_common_factor_with_thin_dyadic_count
          n f hf0 H hH hf theta Q Y i M p.1 p.2 hM hY hQ hxQ
            (by simpa only [mu, delta, U, V] using hthin)
            (cell p) (by rfl) hzero
      have henv : 0 ≤ fullCellElementarySieveEnvelope N (2 * n + 1)
          U V (M : ℝ) mu :=
        fullCellElementarySieveEnvelope_nonnegative_aggregate N (2 * n + 1)
          U V (M : ℝ) mu hN hU hV hMr hmu
      dsimp [cellBase]
      simpa only [mu] using hcount.trans (by nlinarith)
    · have hfullBranch : 1 ≤ 4 * mu / delta := le_of_not_gt hthin
      obtain ⟨d, b, D, f', hdb, hD0, hDhom, hf'0, hfactor, hHD,
          hHf', hcomponents, heval, hz, hcount⟩ :=
        hfull n f hf0 H hH hf theta Q Y i M p.1 p.2 hM hk hY hQ
          hxQ (by simpa only [mu, delta, U, V] using hfullBranch)
          (hbudgets (by simpa only [mu, delta] using hfullBranch))
          (cell p) (by rfl) hzero
      have hb : b ≤ n := by omega
      have hdegree : 2 * b + 1 ≤ 2 * n + 1 := by omega
      have hmono := fullCellElementarySieveEnvelope_mono_degree
        (N := N) (d := 2 * b + 1) (D := 2 * n + 1)
        (U := U) (V := V) (M := (M : ℝ)) (mu := mu) hN hmu hdegree
      calc
        ((cell p).card : ℝ) ≤ 96 * Q * (n : ℝ) +
            8 * fullCellElementarySieveEnvelope N (2 * b + 1)
              U V (M : ℝ) mu := by
          simpa only [cell, U, V, mu] using hcount
        _ ≤ 96 * Q * (n : ℝ) +
            8 * fullCellElementarySieveEnvelope N (2 * n + 1)
              U V (M : ℝ) mu := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hmono (by norm_num))
        _ ≤ cellBase +
            8 * fullCellElementarySieveEnvelope N (2 * n + 1)
              U V (M : ℝ) mu := by
          dsimp [cellBase]
          linarith
  have hsumCells :
      (∑ p ∈ I, ((cell p).card : ℝ)) ≤
        (I.card : ℝ) * cellBase +
          8 * ∑ p ∈ I,
            fullCellElementarySieveEnvelope N (2 * n + 1)
              U V (M : ℝ)
                (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
    calc
      (∑ p ∈ I, ((cell p).card : ℝ)) ≤
          ∑ p ∈ I, (cellBase +
            8 * fullCellElementarySieveEnvelope N (2 * n + 1)
              U V (M : ℝ)
                (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) := by
        exact Finset.sum_le_sum fun p hp => hpointwise p hp
      _ = (I.card : ℝ) * cellBase +
          8 * ∑ p ∈ I,
            fullCellElementarySieveEnvelope N (2 * n + 1)
              U V (M : ℝ)
                (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hsumEnvelope :
      (∑ p ∈ I,
        fullCellElementarySieveEnvelope N (2 * n + 1)
          U V (M : ℝ)
            (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) ≤
        fullCellElementarySieveAggregateEnvelope
          N (2 * n + 1) U V (M : ℝ) := by
    simpa only [P, U, V] using
      sum_fullCellElementarySieveEnvelope_subset_dyadicSourceTargetCellPairs_le
        theta Y i hM hscale hN I hIP (fun _ => 2 * n + 1)
          (by intro p hp; exact le_rfl)
  have hPcardNat := card_dyadicSourceTargetCellPairs_le theta Y i hM hscale
  have hPcard : (P.card : ℝ) ≤ 1348 * (M : ℝ) := by
    dsimp [P]
    exact_mod_cast hPcardNat
  have hIcardNat : I.card ≤ P.card := Finset.card_le_card hIP
  have hIcard : (I.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hIcardNat
  have hconstant :
      (P.card : ℝ) * (H0 : ℝ) + (I.card : ℝ) * cellBase ≤
        (1348 * (M : ℝ)) * ((H0 : ℝ) + cellBase) := by
    calc
      (P.card : ℝ) * (H0 : ℝ) + (I.card : ℝ) * cellBase ≤
          (P.card : ℝ) * (H0 : ℝ) + (P.card : ℝ) * cellBase := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_right hIcard hbase)
      _ = (P.card : ℝ) * ((H0 : ℝ) + cellBase) := by ring
      _ ≤ (1348 * (M : ℝ)) * ((H0 : ℝ) + cellBase) := by
        exact mul_le_mul_of_nonneg_right hPcard (add_nonneg hH0r hbase)
  calc
    ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
        (P.card : ℝ) * (H0 : ℝ) +
          ((heavyCellUnion P cell H0).card : ℝ) := hsparse
    _ ≤ (P.card : ℝ) * (H0 : ℝ) +
          ∑ p ∈ I, ((cell p).card : ℝ) :=
      add_le_add (le_refl _) hheavy
    _ ≤ (P.card : ℝ) * (H0 : ℝ) +
          ((I.card : ℝ) * cellBase +
            8 * ∑ p ∈ I,
              fullCellElementarySieveEnvelope N (2 * n + 1)
                U V (M : ℝ)
                  (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ))) :=
      add_le_add (le_refl _) hsumCells
    _ = ((P.card : ℝ) * (H0 : ℝ) + (I.card : ℝ) * cellBase) +
          8 * ∑ p ∈ I,
            fullCellElementarySieveEnvelope N (2 * n + 1)
              U V (M : ℝ)
                (firstSlopeSupNorm U V (M : ℝ) (p.2 : ℝ)) := by ring
    _ ≤ (1348 * (M : ℝ)) * ((H0 : ℝ) + cellBase) +
          8 * fullCellElementarySieveAggregateEnvelope
            N (2 * n + 1) U V (M : ℝ) := by
      exact add_le_add hconstant
        (mul_le_mul_of_nonneg_left hsumEnvelope (by norm_num))
    _ = 1348 * (M : ℝ) *
          ((H0 : ℝ) + 96 * Q * (n : ℝ) + 16) +
        8 * fullCellElementarySieveAggregateEnvelope
          N (2 * n + 1) U V (M : ℝ) := by
      simp only [cellBase]
      ring

end

end PellPaper
