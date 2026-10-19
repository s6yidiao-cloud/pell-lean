import Pell.GeneralBidegreeAuxiliaryRelation
import Pell.RowScalingTransport

/-!
# Affine transport for general bihomogeneous auxiliary forms

This module relates the standard integral homogeneous evaluation used by
`GeneralBidegreeAuxiliaryRelation` to its rational affine chart.  At the
homogeneous point `((d,e),(v,u))`, the affine coordinates are `(d/e, v/u)`;
the homogeneous value is the affine value multiplied by `e^A u^B`.

This is only an algebraic dehomogenization identity.  It does not identify
these coordinates with any source-specific parametrization, and makes no
height, determinant, or point-counting assertion.
-/

namespace PellPaper

open scoped BigOperators

/-- The rational affine monomial associated to a standard homogeneous
bidegree-`(A,B)` monomial.  The exponent convention is chosen so that the
homogeneous coordinates `(d,e)` and `(v,u)` dehomogenize to `d / e` and
`v / u`, respectively. -/
def generalBidegreeFormAffineMonomial (A B : ℕ) (x y : ℚ)
    (ab : generalBidegreeFormIndex A B) : ℚ :=
  x ^ (A - ab.1.1) * y ^ (B - ab.2.1)

/-- Rational affine evaluation of an integral standard bidegree-`(A,B)`
coefficient vector. -/
def generalBidegreeFormAffineEval (A B : ℕ)
    (c : generalBidegreeFormIndex A B → ℤ) (x y : ℚ) : ℚ :=
  ∑ ab, (c ab : ℚ) * generalBidegreeFormAffineMonomial A B x y ab

/-- The source exponent selected by a standard coefficient position is at
most the total source degree. -/
theorem generalBidegreeFormIndex_source_le (A B : ℕ)
    (ab : generalBidegreeFormIndex A B) : ab.1.1 ≤ A :=
  Nat.le_of_lt_succ ab.1.2

/-- The target exponent selected by a standard coefficient position is at
most the total target degree. -/
theorem generalBidegreeFormIndex_target_le (A B : ℕ)
    (ab : generalBidegreeFormIndex A B) : ab.2.1 ≤ B :=
  Nat.le_of_lt_succ ab.2.2

/-- One homogeneous monomial is the affine monomial multiplied by the two
homogenizing denominator factors. -/
theorem cast_generalBidegreeFormMonomial_eq_homogenizingFactor_mul_affine
    (A B : ℕ) (d e v u : ℤ) (ab : generalBidegreeFormIndex A B)
    (he : (e : ℚ) ≠ 0) (hu : (u : ℚ) ≠ 0) :
    (generalBidegreeFormMonomial A B ((d, e), (v, u)) ab : ℚ) =
      ((e : ℚ) ^ A * (u : ℚ) ^ B) *
        generalBidegreeFormAffineMonomial A B
          ((d : ℚ) / (e : ℚ)) ((v : ℚ) / (u : ℚ)) ab := by
  have hA : A - ab.1.1 + ab.1.1 = A :=
    Nat.sub_add_cancel (generalBidegreeFormIndex_source_le A B ab)
  have hB : B - ab.2.1 + ab.2.1 = B :=
    Nat.sub_add_cancel (generalBidegreeFormIndex_target_le A B ab)
  have hepow : (e : ℚ) ^ (A - ab.1.1 + ab.1.1) = (e : ℚ) ^ A :=
    congrArg (fun n : ℕ => (e : ℚ) ^ n) hA
  have hupow : (u : ℚ) ^ (B - ab.2.1 + ab.2.1) = (u : ℚ) ^ B :=
    congrArg (fun n : ℕ => (u : ℚ) ^ n) hB
  simp only [generalBidegreeFormMonomial, generalBidegreeFormSource,
    generalBidegreeFormTarget, generalBidegreeFormAffineMonomial,
    Int.cast_mul, Int.cast_pow]
  rw [← hepow, ← hupow, pow_add, pow_add, div_pow, div_pow]
  field_simp [he, hu]

/-- The homogeneous integral form evaluation, cast to the rationals, equals
the affine evaluation times the expected nonzero homogenizing factor. -/
theorem cast_generalBidegreeFormEval_eq_homogenizingFactor_mul_affineEval
    (A B : ℕ) (c : generalBidegreeFormIndex A B → ℤ)
    (d e v u : ℤ) (he : (e : ℚ) ≠ 0) (hu : (u : ℚ) ≠ 0) :
    (generalBidegreeFormEval A B c ((d, e), (v, u)) : ℚ) =
      ((e : ℚ) ^ A * (u : ℚ) ^ B) *
        generalBidegreeFormAffineEval A B c
          ((d : ℚ) / (e : ℚ)) ((v : ℚ) / (u : ℚ)) := by
  simp only [generalBidegreeFormEval, generalBidegreeFormAffineEval,
    Int.cast_sum, Int.cast_mul]
  simp_rw [cast_generalBidegreeFormMonomial_eq_homogenizingFactor_mul_affine
    A B d e v u _ he hu]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  ring

/-- Therefore homogeneous vanishing at nonzero denominator coordinates
implies vanishing of the associated rational affine evaluation. -/
theorem generalBidegreeFormAffineEval_eq_zero_of_homogeneousEval_eq_zero
    (A B : ℕ) (c : generalBidegreeFormIndex A B → ℤ)
    (d e v u : ℤ) (he : (e : ℚ) ≠ 0) (hu : (u : ℚ) ≠ 0)
    (hzero : generalBidegreeFormEval A B c ((d, e), (v, u)) = 0) :
    generalBidegreeFormAffineEval A B c
      ((d : ℚ) / (e : ℚ)) ((v : ℚ) / (u : ℚ)) = 0 := by
  have hcast : (generalBidegreeFormEval A B c ((d, e), (v, u)) : ℚ) = 0 := by
    exact_mod_cast hzero
  rw [cast_generalBidegreeFormEval_eq_homogenizingFactor_mul_affineEval
    A B c d e v u he hu] at hcast
  have hfactor : (e : ℚ) ^ A * (u : ℚ) ^ B ≠ 0 :=
    mul_ne_zero (pow_ne_zero A he) (pow_ne_zero B hu)
  exact (mul_eq_zero.mp hcast).resolve_left hfactor

/-- The first rational affine coordinate of an integral homogeneous point. -/
def generalBidegreeFormAffineSourceCoordinate (p : GeneralBidegreeFormPoint) : ℚ :=
  (p.1.1 : ℚ) / (p.1.2 : ℚ)

/-- The second rational affine coordinate of an integral homogeneous point. -/
def generalBidegreeFormAffineTargetCoordinate (p : GeneralBidegreeFormPoint) : ℚ :=
  (p.2.1 : ℚ) / (p.2.2 : ℚ)

/-- The rational factor which homogenizes the affine chart at an integral
point for bidegree `(A,B)`. -/
def generalBidegreeFormHomogenizingFactor (A B : ℕ)
    (p : GeneralBidegreeFormPoint) : ℚ :=
  (p.1.2 : ℚ) ^ A * (p.2.2 : ℚ) ^ B

/-- The rational affine evaluation matrix associated to a family of integral
homogeneous points. -/
def generalBidegreeFormAffineEvaluationMatrix {ι : Type*} (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex A B) ℚ :=
  fun r ab => generalBidegreeFormAffineMonomial A B
    (generalBidegreeFormAffineSourceCoordinate (points r))
    (generalBidegreeFormAffineTargetCoordinate (points r)) ab

/-- Rowwise multiplication of the rational affine evaluation matrix by the
explicit homogenizing factor is exactly the rationalization of the integral
homogeneous evaluation matrix.  This is a denominator-clearing identity, not
a claim that a source-specific transformed matrix has this form. -/
theorem rowScale_generalBidegreeFormAffineEvaluationMatrix_eq_rationalizedHomogeneous
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (hden : ∀ r, (points r).1.2 ≠ 0 ∧ (points r).2.2 ≠ 0) :
    rowScale (fun r => generalBidegreeFormHomogenizingFactor A B (points r))
      (generalBidegreeFormAffineEvaluationMatrix A B points) =
      (generalBidegreeFormEvaluationMatrix A B points).map (algebraMap ℤ ℚ) := by
  ext r ab
  rcases hpoint : points r with ⟨⟨d, e⟩, ⟨v, u⟩⟩
  have heZ : e ≠ 0 := by
    simpa [hpoint] using (hden r).1
  have huZ : u ≠ 0 := by
    simpa [hpoint] using (hden r).2
  have he : (e : ℚ) ≠ 0 := by
    exact_mod_cast heZ
  have hu : (u : ℚ) ≠ 0 := by
    exact_mod_cast huZ
  simpa [rowScale, generalBidegreeFormHomogenizingFactor,
    generalBidegreeFormAffineEvaluationMatrix,
    generalBidegreeFormAffineSourceCoordinate,
    generalBidegreeFormAffineTargetCoordinate,
    generalBidegreeFormEvaluationMatrix, hpoint] using
    (cast_generalBidegreeFormMonomial_eq_homogenizingFactor_mul_affine
      A B d e v u ab he hu).symm

end PellPaper
