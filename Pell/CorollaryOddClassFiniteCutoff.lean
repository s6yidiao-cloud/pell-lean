import Pell.CorollaryOddClassPointwise
import Pell.ClassAverageReduction
import Pell.CauchyExceptional
import Pell.FundamentalDiscriminantPellRegulator

/-!
# A finite one-cutoff reduction for Corollary 1.2

This module performs the finite Cauchy--Schwarz and cutoff bookkeeping in the
odd class-number argument.  It assumes only numerical majorants for the
selected-L second moment and the genus-weighted first moment at one fixed
cutoff.  The small-regulator filter is included in the already formalized Pell
exceptional set at exponent `T + 1`; the complementary filter is bounded by
the unrestricted weighted first moment.

The final theorem instantiates `finite_sum_class_bound_of_cutoff_numerators`
with the concrete Pell-order regulator and its proved lower bound `1 / 2`.
No genus theorem or moment estimate is asserted here: the genus pointwise
bound and both moment inequalities remain explicit premises.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The non-strict low-regulator filter at `T` lies in the strict filter at
`T + 1`, whose cardinality is controlled by `E (T + 1) X`. -/
theorem fundamentalDiscriminantsBelow_pellOrderRegulator_le_filter_card_le_E
    {X T : ℝ} (hX : 0 ≤ X) :
    ((((fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D ≤ T)).card : ℕ) : ℝ) ≤
        E (T + 1) X := by
  let slow := (fundamentalDiscriminantsBelow X).filter
    (fun D ↦ pellOrderRegulator D ≤ T)
  let sstrict := (fundamentalDiscriminantsBelow X).filter
    (fun D ↦ pellOrderRegulator D < T + 1)
  have hsubset : slow ⊆ sstrict := by
    intro D hD
    obtain ⟨hDX, hreg⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨hDX, by linarith⟩
  calc
    ((slow.card : ℕ) : ℝ) ≤ ((sstrict.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ E (T + 1) X :=
      fundamentalDiscriminantsBelow_pellOrderRegulatorFilter_card_le_E hX

/-- Cauchy--Schwarz bounds the selected-L numerator on the low-regulator
filter by the square root of the Pell exceptional count times any total
second-moment majorant. -/
theorem selectedKroneckerLValue_lowPellOrderRegulatorSum_le
    (X T M : ℝ) (hX : 0 ≤ X)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M) :
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D ≤ T),
        selectedKroneckerLValue D) ≤
      Real.sqrt (E (T + 1) X * M) := by
  let s := fundamentalDiscriminantsBelow X
  let slow := s.filter (fun D ↦ pellOrderRegulator D ≤ T)
  apply exceptional_sum_le_sqrt_of_card_le s slow selectedKroneckerLValue
    (E (T + 1) X) M
  · exact Finset.filter_subset _ _
  · dsimp [slow, s]
    exact fundamentalDiscriminantsBelow_pellOrderRegulator_le_filter_card_le_E
      hX
  · simpa [s] using hmoment

/-- The genus weight is at most one, so the low-regulator numerator occurring
in the pointwise odd-class bound has the same Cauchy majorant, up to its
explicit factor `24 * Cgenus`. -/
theorem oddClassWeightedSelectedLValue_lowPellOrderRegulatorSum_le
    (Cgenus X T M : ℝ) (hCgenus : 0 ≤ Cgenus) (hX : 0 ≤ X)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M) :
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D ≤ T),
        oddClassWeightedSelectedLValue Cgenus D) ≤
      24 * Cgenus * Real.sqrt (E (T + 1) X * M) := by
  have hfactor : 0 ≤ 24 * Cgenus := mul_nonneg (by norm_num) hCgenus
  calc
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
        (fun D ↦ pellOrderRegulator D ≤ T),
          oddClassWeightedSelectedLValue Cgenus D) ≤
      ∑ D ∈ (fundamentalDiscriminantsBelow X).filter
        (fun D ↦ pellOrderRegulator D ≤ T),
          (24 * Cgenus) * selectedKroneckerLValue D := by
      apply Finset.sum_le_sum
      intro D _hD
      unfold oddClassWeightedSelectedLValue
      calc
        24 * Cgenus * genusWeight D * selectedKroneckerLValue D =
            (24 * Cgenus) *
              (genusWeight D * selectedKroneckerLValue D) := by ring
        _ ≤ (24 * Cgenus) * (1 * selectedKroneckerLValue D) := by
          apply mul_le_mul_of_nonneg_left _ hfactor
          exact mul_le_mul_of_nonneg_right (genusWeight_le_one D)
            (selectedKroneckerLValue_nonneg D)
        _ = (24 * Cgenus) * selectedKroneckerLValue D := by ring
    _ = (24 * Cgenus) *
        (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
          (fun D ↦ pellOrderRegulator D ≤ T),
            selectedKroneckerLValue D) := by
      rw [Finset.mul_sum]
    _ ≤ (24 * Cgenus) * Real.sqrt (E (T + 1) X * M) := by
      exact mul_le_mul_of_nonneg_left
        (selectedKroneckerLValue_lowPellOrderRegulatorSum_le X T M hX hmoment)
        hfactor
    _ = 24 * Cgenus * Real.sqrt (E (T + 1) X * M) := by ring

/-- Any majorant for the total genus-weighted first moment bounds the
high-regulator numerator.  Only nonnegativity and filter inclusion are used. -/
theorem oddClassWeightedSelectedLValue_highPellOrderRegulatorSum_le
    (Cgenus X T W : ℝ) (hCgenus : 0 ≤ Cgenus)
    (hweightedFirst :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        genusWeight D * selectedKroneckerLValue D) ≤ W) :
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
      (fun D ↦ T < pellOrderRegulator D),
        oddClassWeightedSelectedLValue Cgenus D) ≤
      24 * Cgenus * W := by
  have hfactor : 0 ≤ 24 * Cgenus := mul_nonneg (by norm_num) hCgenus
  have hsubset :
      ∑ D ∈ (fundamentalDiscriminantsBelow X).filter
          (fun D ↦ T < pellOrderRegulator D),
            genusWeight D * selectedKroneckerLValue D ≤
        ∑ D ∈ fundamentalDiscriminantsBelow X,
          genusWeight D * selectedKroneckerLValue D := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro D _ _
    exact mul_nonneg (genusWeight_nonneg D)
      (selectedKroneckerLValue_nonneg D)
  calc
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
        (fun D ↦ T < pellOrderRegulator D),
          oddClassWeightedSelectedLValue Cgenus D) =
      (24 * Cgenus) *
        (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
          (fun D ↦ T < pellOrderRegulator D),
            genusWeight D * selectedKroneckerLValue D) := by
      unfold oddClassWeightedSelectedLValue
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _hD
      ring
    _ ≤ (24 * Cgenus) *
        (∑ D ∈ fundamentalDiscriminantsBelow X,
          genusWeight D * selectedKroneckerLValue D) :=
      mul_le_mul_of_nonneg_left hsubset hfactor
    _ ≤ (24 * Cgenus) * W :=
      mul_le_mul_of_nonneg_left hweightedFirst hfactor
    _ = 24 * Cgenus * W := by ring

/-- The complete finite one-cutoff estimate for the exact
discriminant-indexed odd class-number sum.

`M` majorizes the unweighted selected-L second moment and `W` majorizes the
total genus-weighted selected-L first moment at this same `X`.  The only
arithmetic premise is the explicitly named pointwise genus bound. -/
theorem positiveFundamentalDiscriminantOddClassSum_le_oneCutoff
    (Cgenus X T M W : ℝ)
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hX : 3 ≤ X) (hT : (1 / 2 : ℝ) ≤ T)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M)
    (hweightedFirst :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        genusWeight D * selectedKroneckerLValue D) ≤ W) :
    positiveFundamentalDiscriminantOddClassSum X ≤
      (Real.sqrt X / Real.log X) *
        (48 * Cgenus * Real.sqrt (E (T + 1) X * M) +
          (24 * Cgenus * W) / T) := by
  have hA : 0 ≤ Real.sqrt X / Real.log X :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
  have hr : ∀ D ∈ fundamentalDiscriminantsBelow X,
      (1 / 2 : ℝ) ≤ pellOrderRegulator D := by
    intro D hD
    exact (one_half_lt_pellOrderRegulator
      (mem_fundamentalDiscriminantsBelow.mp hD).1).le
  have hfinite := finite_sum_class_bound_of_cutoff_numerators
    (fundamentalDiscriminantsBelow X)
    (fun D ↦ (positiveFundamentalDiscriminantOddClassNumber D : ℝ))
    (oddClassWeightedSelectedLValue Cgenus) pellOrderRegulator
    (Real.sqrt X / Real.log X) (1 / 2 : ℝ) T
    (24 * Cgenus * Real.sqrt (E (T + 1) X * M))
    (24 * Cgenus * W)
    hA
    (fun D _hD ↦ oddClassWeightedSelectedLValue_nonneg hgenus.1 D)
    hr (by norm_num) hT
    (fun D hD ↦
      positiveFundamentalDiscriminantOddClassNumber_le_cutoff_weightedLValue_div_pellOrderRegulator
        hgenus hD)
    (oddClassWeightedSelectedLValue_lowPellOrderRegulatorSum_le
      Cgenus X T M hgenus.1 (by linarith) hmoment)
    (oddClassWeightedSelectedLValue_highPellOrderRegulatorSum_le
      Cgenus X T W hgenus.1 hweightedFirst)
  unfold positiveFundamentalDiscriminantOddClassSum
  calc
    (∑ D ∈ fundamentalDiscriminantsBelow X,
        (positiveFundamentalDiscriminantOddClassNumber D : ℝ)) ≤
      (Real.sqrt X / Real.log X) *
        ((24 * Cgenus * Real.sqrt (E (T + 1) X * M)) / (1 / 2 : ℝ) +
          (24 * Cgenus * W) / T) := hfinite
    _ = (Real.sqrt X / Real.log X) *
        (48 * Cgenus * Real.sqrt (E (T + 1) X * M) +
          (24 * Cgenus * W) / T) := by ring

/-- The same finite estimate for the literal sum over actual real quadratic
field isomorphism classes, obtained only after invoking the proved exact
field/discriminant transport. -/
theorem realQuadraticFieldOddClassSum_le_oneCutoff
    (Cgenus X T M W : ℝ)
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hX : 3 ≤ X) (hT : (1 / 2 : ℝ) ≤ T)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M)
    (hweightedFirst :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        genusWeight D * selectedKroneckerLValue D) ≤ W) :
    realQuadraticFieldOddClassSum X ≤
      (Real.sqrt X / Real.log X) *
        (48 * Cgenus * Real.sqrt (E (T + 1) X * M) +
          (24 * Cgenus * W) / T) := by
  rw [realQuadraticFieldOddClassSum_eq_positiveFundamentalDiscriminantOddClassSum]
  exact positiveFundamentalDiscriminantOddClassSum_le_oneCutoff
    Cgenus X T M W hgenus hX hT hmoment hweightedFirst

end

end PellPaper
