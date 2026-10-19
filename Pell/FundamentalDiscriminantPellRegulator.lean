import Pell.FundamentalDiscriminantCutoff
import Pell.QuadraticPellRegulatorBridge

/-!
# The actual Pell regulator on positive fundamental discriminants

The class-number proof ultimately needs a regulator parameter on positive
fundamental discriminants.  Before comparing it to the fundamental unit of a
maximal order, there is an entirely concrete parameter already available in
the project: the normalized logarithm of the unique fundamental Pell solution
in `ℤ[√D]`.

This file makes that parameter into a total function on natural numbers and
proves that its small-cutoff subfamily is bounded directly by the existing
Pell exceptional count.  No field-unit comparison, class-number model, or
analytic estimate is used.
-/

namespace PellPaper

noncomputable section

/-- The unique positive fundamental Pell solution attached to a positive
fundamental discriminant. -/
noncomputable def fundamentalPellSolution (D : ℕ)
    (hD : PositiveFundamentalDiscriminant D) : Pell.Solution₁ (D : ℤ) :=
  Classical.choose (existsUnique_isFundamental_of_positiveFundamentalDiscriminant hD)

/-- The chosen Pell solution is fundamental. -/
theorem fundamentalPellSolution_isFundamental (D : ℕ)
    (hD : PositiveFundamentalDiscriminant D) :
    Pell.IsFundamental (fundamentalPellSolution D hD) := by
  exact (Classical.choose_spec
    (existsUnique_isFundamental_of_positiveFundamentalDiscriminant hD)).1

/-- A total discriminant-indexed normalized Pell regulator.  Away from the
positive fundamental discriminants its value is set to zero; all later uses
are restricted to the fundamental-discriminant family. -/
noncomputable def pellOrderRegulator (D : ℕ) : ℝ :=
  by
    classical
    exact if hD : PositiveFundamentalDiscriminant D then
      pellNormalizedLog (fundamentalPellSolution D hD)
    else 0

/-- On the intended family, the total regulator is the normalized logarithm
of its actual fundamental Pell solution. -/
theorem pellOrderRegulator_eq_pellNormalizedLog {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) :
    pellOrderRegulator D = pellNormalizedLog (fundamentalPellSolution D hD) := by
  simp [pellOrderRegulator, hD]

/-- A strict cutoff on the concrete Pell regulator produces the literal Pell
small-fundamental-solution condition, with no loss in the exponent. -/
theorem smallFundamentalSolution_of_pellOrderRegulator_lt
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) (t : ℝ)
    (hreg : pellOrderRegulator D < t) :
    SmallFundamentalSolution t D := by
  rw [pellOrderRegulator_eq_pellNormalizedLog hD] at hreg
  exact (smallFundamentalSolution_iff_pellNormalizedLog_le hD
    (fundamentalPellSolution_isFundamental D hD) t).mpr hreg.le

/-- The small-Pell-regulator part of the genuine fundamental-discriminant
family lies in the Pell exceptional set at the corresponding natural cutoff. -/
theorem fundamentalDiscriminantsBelow_pellOrderRegulatorFilter_subset_exceptionalSet
    {X t : ℝ} (hX : 0 ≤ X) :
    (fundamentalDiscriminantsBelow X).filter (fun D ↦ pellOrderRegulator D < t) ⊆
      exceptionalSet t ⌊X⌋₊ := by
  intro D hmem
  obtain ⟨hDX, hreg⟩ := Finset.mem_filter.mp hmem
  obtain ⟨hD, _⟩ := mem_fundamentalDiscriminantsBelow.mp hDX
  have hDone : 1 < D := hD.1
  exact mem_exceptionalSet.mpr
    ⟨hDone.le,
      fundamentalDiscriminant_le_floor_of_mem hX hDX,
      smallFundamentalSolution_of_pellOrderRegulator_lt hD t hreg⟩

/-- The concrete regulator-small fundamental-discriminant family is bounded
by the real-cutoff Pell exceptional count. -/
theorem fundamentalDiscriminantsBelow_pellOrderRegulatorFilter_card_le_E
    {X t : ℝ} (hX : 0 ≤ X) :
    (((fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤ E t X := by
  have hcard := Finset.card_le_card
    (fundamentalDiscriminantsBelow_pellOrderRegulatorFilter_subset_exceptionalSet hX
      (t := t))
  change (((fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤
    ((exceptionalSet t ⌊X⌋₊).card : ℝ)
  exact_mod_cast hcard

/-- The same bound written in the class-side exceptional-set notation.  It
discharges the finite injection/cutoff premise of the class pipeline when the
regulator parameter is the concrete Pell-order regulator. -/
theorem classRegulatorExceptionalSet_pellOrderRegulator_card_le_E
    {X t : ℝ} (hX : 0 ≤ X) :
    ((classRegulatorExceptionalSet (fundamentalDiscriminantsBelow X) id
      pellOrderRegulator ⌊X⌋₊ t).card : ℝ) ≤ E t X := by
  rw [classRegulatorExceptionalSet_fundamentalDiscriminantsBelow_eq_regulatorFilter
    X t pellOrderRegulator hX]
  exact fundamentalDiscriminantsBelow_pellOrderRegulatorFilter_card_le_E hX

end

end PellPaper
