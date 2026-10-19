import Pell.CorollaryOddClassBrowningChanConditional
import Pell.CorollaryOddClassTauCetiGenus
import Pell.Main3ElementaryFinalAssembly

/-!
# Conditional capstone for Corollary 1.2

TauCeti genus theory, the uniform Pell exceptional estimate, and the selected
L-value second moment are all proved in imported production modules.  Thus
the exact all-`X` odd-class assertion now follows from one honest remaining
analytic interface: the published Browning--Chan weighted baseline moment.
-/

namespace PellPaper

open Filter Asymptotics

noncomputable section

/-- Exact Corollary 1.2 assertion conditional only on the named published
Browning--Chan weighted moment.  This theorem is intentionally named as a
conditional result; it does not assert or axiomatize that moment. -/
theorem realQuadraticFieldOddClassAverageAssertion_conditional_on_browningChanMoment
    (hBrowningChan : BrowningChanOddClassBaselineMoment) :
    RealQuadraticFieldOddClassAverageAssertion := by
  exact realQuadraticFieldOddClassAverageAssertion_of_browningChan
    oddClassGenusPointwiseBound_four_tauceti_proved hBrowningChan
      uniformExceptionalEstimate_one_div_6400_elementary_proved

/-- The exact Corollary 1.2 assertion from the source's literal `\ll`
formulation of the Browning--Chan weighted moment.  This remains a conditional
theorem: its sole hypothesis is merely expressed with Mathlib's `IsBigO`
notation instead of the equivalent explicit eventual constant. -/
theorem realQuadraticFieldOddClassAverageAssertion_conditional_on_browningChanIsBigO
    (hBrowningChan :
      (fun X : ℝ ↦ browningChanOddClassBaselineSum X) =O[atTop]
        browningChanOddClassBaselineScale) :
    RealQuadraticFieldOddClassAverageAssertion := by
  exact
    realQuadraticFieldOddClassAverageAssertion_conditional_on_browningChanMoment
      (browningChanOddClassBaselineMoment_iff_isBigO.mpr hBrowningChan)

end

end PellPaper
