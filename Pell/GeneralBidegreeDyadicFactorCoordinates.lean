import Pell.GeneralBidegreeAffineTransport
import Pell.DyadicCountingReduction

/-!
# Dyadic factor coordinates for homogeneous auxiliary forms

This file connects the standard homogeneous bidegree-`(A,B)` form to the
factor-tuple coordinates used by the dyadic counting reduction.  The source
pair is `(d,e)` and the target pair is `(v,u)`, so the associated affine
coordinates are `d/e` and `v/u`.

Only this exact dehomogenization is proved here.  No determinant estimate,
height bound, factorization, or point-counting assertion is included.
-/

namespace PellPaper

/-- The actual integral homogeneous point attached to the factor tuple
`(d,e,u,v)`: the target pair is deliberately ordered as `(v,u)`. -/
def dyadicFactorTupleToGeneralBidegreeFormPoint (p : ℕ × ℕ × ℕ × ℕ) :
    GeneralBidegreeFormPoint :=
  (((p.1 : ℤ), (p.2.1 : ℤ)), ((p.2.2.2 : ℤ), (p.2.2.1 : ℤ)))

/-- Membership in the dyadic factor-tuple set supplies the positive source
and target denominators needed for the rational coordinates `d/e` and
`v/u`. -/
theorem dyadicFactorTuple_rational_denominators_ne_zero
    {θ : ℝ} {Y : ℕ} {p : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ dyadicFactorTuples θ Y) :
    (p.2.1 : ℚ) ≠ 0 ∧ (p.2.2.1 : ℚ) ≠ 0 := by
  obtain ⟨_hd, he, hu, _hv, _⟩ := mem_dyadicFactorTuples.mp hp
  constructor
  · exact_mod_cast ne_of_gt he
  · exact_mod_cast ne_of_gt hu

/-- For every actual tuple in the dyadic factor family, homogeneous
vanishing at the integral point `((d,e),(v,u))` implies affine vanishing at
the source-coordinate ratios `(d/e,v/u)`.  The tuple order is
`(d,e,u,v)`, hence the intentionally reversed target pair `(v,u)`. -/
theorem generalBidegreeFormAffineEval_eq_zero_of_mem_dyadicFactorTuples
    {θ : ℝ} {Y : ℕ} (A B : ℕ)
    (c : generalBidegreeFormIndex A B → ℤ) (p : ℕ × ℕ × ℕ × ℕ)
    (hp : p ∈ dyadicFactorTuples θ Y)
    (hvanish : generalBidegreeFormEval A B c
      (dyadicFactorTupleToGeneralBidegreeFormPoint p) = 0) :
    generalBidegreeFormAffineEval A B c
      ((p.1 : ℚ) / (p.2.1 : ℚ))
      ((p.2.2.2 : ℚ) / (p.2.2.1 : ℚ)) = 0 := by
  obtain ⟨he, hu⟩ := dyadicFactorTuple_rational_denominators_ne_zero hp
  have he' : ((p.2.1 : ℤ) : ℚ) ≠ 0 := by
    simpa using he
  have hu' : ((p.2.2.1 : ℤ) : ℚ) ≠ 0 := by
    simpa using hu
  simpa [dyadicFactorTupleToGeneralBidegreeFormPoint] using
    generalBidegreeFormAffineEval_eq_zero_of_homogeneousEval_eq_zero
      A B c (p.1 : ℤ) (p.2.1 : ℤ) (p.2.2.2 : ℤ) (p.2.2.1 : ℤ)
      he' hu' hvanish

end PellPaper
