import Pell.QuadraticKroneckerCharacterFullQuadraticity

/-!
# Complex quadraticity of the positive-fundamental-discriminant character

The integral branchwise character is quadratic in
`QuadraticKroneckerCharacterFullQuadraticity`.  This module transports that
fact through the already-defined complex extension.  It establishes only
complex quadraticity and the resulting pointwise-square identity; it makes no
claim about primitivity, conductor, agreement with an all-integer Kronecker
symbol, or an `L`-function factorization.
-/

namespace PellPaper

noncomputable section

/-- The complex extension of the selected character at a positive fundamental
discriminant is quadratic. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_isQuadratic
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD).IsQuadratic := by
  exact
    kroneckerCharacterAtPositiveFundamentalDiscriminantC_isQuadratic_of_integralQuadratic
      D hD (kroneckerCharacterAtPositiveFundamentalDiscriminant_isQuadratic D hD)

/-- The complex extension of the selected character at a positive fundamental
discriminant has square equal to one. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_sq_eq_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD ^ 2 = 1 := by
  exact
    kroneckerCharacterAtPositiveFundamentalDiscriminantC_sq_eq_one_of_integralQuadratic
      D hD (kroneckerCharacterAtPositiveFundamentalDiscriminant_isQuadratic D hD)

end

end PellPaper
