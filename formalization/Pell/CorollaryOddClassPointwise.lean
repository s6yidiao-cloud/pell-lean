import Pell.CorollaryOddPartGenusAlgebra
import Pell.RealQuadraticFieldOddClassSum
import Pell.QuadraticSelectedLValueNormalizedRegulator
import Pell.MaximalOrderFundamentalUnitClassBridge

/-!
# The pointwise odd-class bound used in Corollary 1.2

This module separates genus theory from the already formalized class-number
formula and unit comparison.  `OddClassGenusPointwiseBound Cgenus` is the
single genus-theory interface consumed below.  The source's narrow-class
formulation supplies it with `Cgenus = 2`; a wide-class genus theorem may
instead supply it with a different absolute constant.

Once that interface is available, all remaining statements in this file are
proved.  In particular the exact odd part of the actual ordinary class number
is bounded by a genus-weighted selected L-value divided by the concrete Pell
regulator, uniformly for every strict real discriminant cutoff.
-/

namespace PellPaper

noncomputable section

open IntegralBinaryQuadraticForm

/-- A constant-factor genus bound for the exact odd part of the actual
ordinary class number.  This is a proposition, not an axiom. -/
def OddClassGenusPointwiseBound (Cgenus : ℝ) : Prop :=
  0 ≤ Cgenus ∧
    ∀ (D : ℕ) (_hD : PositiveFundamentalDiscriminant D),
      (positiveFundamentalDiscriminantOddClassNumber D : ℝ) ≤
        Cgenus * genusWeight D *
          (Nat.card (ProperFormClass (D : ℤ)) : ℝ)

/-- The two exact source-level genus interfaces imply the downstream
constant-factor interface with constant two. -/
theorem oddClassGenusPointwiseBound_two_of_properFormClassGenus
    (hcompat : ProperFormClassOddPartCompatibility)
    (hgenus : ProperFormClassGenusDivisibility) :
    OddClassGenusPointwiseBound 2 := by
  refine ⟨by norm_num, ?_⟩
  intro D hD
  exact classNumberOddPart_cast_le_two_mul_genusWeight_mul_properFormClassCard
    hcompat hgenus D hD

/-- The genus-weighted selected L-value numerator after the factor-six unit
comparison and the factor-four uniform `sqrt D / log D` comparison. -/
def oddClassWeightedSelectedLValue (Cgenus : ℝ) (D : ℕ) : ℝ :=
  24 * Cgenus * genusWeight D * selectedKroneckerLValue D

theorem oddClassWeightedSelectedLValue_nonneg {Cgenus : ℝ}
    (hCgenus : 0 ≤ Cgenus) (D : ℕ) :
    0 ≤ oddClassWeightedSelectedLValue Cgenus D := by
  unfold oddClassWeightedSelectedLValue
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hCgenus) (genusWeight_nonneg D))
    (selectedKroneckerLValue_nonneg D)

/-- The exact pointwise bridge used by the one-cutoff argument.  Apart from
the explicitly supplied genus bound, every ingredient is already proved for
the project's actual quadratic field, selected L-value, and Pell regulator. -/
theorem positiveFundamentalDiscriminantOddClassNumber_le_cutoff_weightedLValue_div_pellOrderRegulator
    {Cgenus X : ℝ} (hgenus : OddClassGenusPointwiseBound Cgenus)
    {D : ℕ} (hDX : D ∈ fundamentalDiscriminantsBelow X) :
    (positiveFundamentalDiscriminantOddClassNumber D : ℝ) ≤
      (Real.sqrt X / Real.log X) *
        (oddClassWeightedSelectedLValue Cgenus D / pellOrderRegulator D) := by
  have hD := (mem_fundamentalDiscriminantsBelow.mp hDX).1
  have hbase : 0 ≤ Real.sqrt X / Real.log X := by
    have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast hD.1
    have hDXreal := (mem_fundamentalDiscriminantsBelow.mp hDX).2
    have hXone : 1 < X := by linarith
    exact div_nonneg (Real.sqrt_nonneg _) (Real.log_pos hXone).le
  have hweight : 0 ≤ Cgenus * genusWeight D :=
    mul_nonneg hgenus.1 (genusWeight_nonneg D)
  have hL4 : 0 ≤ 4 * selectedKroneckerLValue D := by
    exact mul_nonneg (by norm_num) (selectedKroneckerLValue_nonneg D)
  have hform :=
    properFormClass_card_le_cutoff_selectedLValue_div_normalizedRegulator X D hDX
  have hdenom :=
    div_maximalOrderFundamentalUnitRegulator_le_six_mul_div_pellOrderRegulator
      hD hL4
  calc
    (positiveFundamentalDiscriminantOddClassNumber D : ℝ) ≤
        Cgenus * genusWeight D *
          (Nat.card (ProperFormClass (D : ℤ)) : ℝ) := hgenus.2 D hD
    _ ≤ Cgenus * genusWeight D *
        ((Real.sqrt X / Real.log X) *
          ((4 * selectedKroneckerLValue D) /
            maximalOrderFundamentalUnitRegulator D)) :=
      mul_le_mul_of_nonneg_left hform hweight
    _ ≤ Cgenus * genusWeight D *
        ((Real.sqrt X / Real.log X) *
          (6 * (4 * selectedKroneckerLValue D) / pellOrderRegulator D)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdenom hbase) hweight
    _ = (Real.sqrt X / Real.log X) *
        (oddClassWeightedSelectedLValue Cgenus D / pellOrderRegulator D) := by
      unfold oddClassWeightedSelectedLValue
      ring

end

end PellPaper
