import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Real.Basic

/-!
# The literal finite odd Jacobi reciprocal polynomial

The sum ranges over the positive odd natural integers at most `N`. The
numerator `d` is arbitrary; no discriminant or coprimality assumption is built
into the definition.
-/

open scoped BigOperators

namespace PellPaper

/-- The real reciprocal polynomial formed from the odd Jacobi coefficients. -/
noncomputable def oddJacobiReciprocalPolynomial (d N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter Odd,
    (jacobiSym (d : ℤ) n : ℝ) / (n : ℝ)

end PellPaper
