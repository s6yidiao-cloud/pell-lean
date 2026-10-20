import Pell.GeneralBidegreeAuxiliaryRelation

/-!
# The `(1,B)` specialization of general bihomogeneous evaluation

The general bidegree convention specializes at source degree `1` to the
two-layer convention already used in the balanced determinant route.  The
coefficient index types are definitionally the same (`Fin 2 × Fin (B+1)`),
and this module proves equality of the resulting monomials, form evaluations,
and evaluation matrices.

This is only an exact finite algebraic identification.  It makes no
determinant, rank, height, coordinate-transport, or counting claim.
-/

namespace PellPaper

open scoped BigOperators

/-- The general coefficient index at source degree one is definitionally the
two-layer coefficient index. -/
def generalBidegreeOneIndexEquivTwoLayer (B : ℕ) :
    generalBidegreeFormIndex 1 B ≃ twoLayerFormIndex B :=
  Equiv.refl _

/-- At degree one, the general homogeneous source monomial agrees with the
two-layer source coordinate. -/
theorem generalBidegreeFormSource_one_eq_twoLayerFormSource
    (x : ℤ × ℤ) (a : Fin 2) :
    generalBidegreeFormSource 1 x a = twoLayerFormSource x a := by
  fin_cases a <;> simp [generalBidegreeFormSource, twoLayerFormSource]

/-- The target monomial conventions agree literally. -/
theorem generalBidegreeFormTarget_eq_twoLayerFormTarget
    (B : ℕ) (y : ℤ × ℤ) (b : Fin (B + 1)) :
    generalBidegreeFormTarget B y b = twoLayerFormTarget B y b := rfl

/-- The general `(1,B)` monomial is the existing two-layer monomial under the
definitional coefficient-index identification. -/
theorem generalBidegreeFormMonomial_one_eq_twoLayerFormMonomial
    (B : ℕ) (p : TwoLayerFormPoint) (ab : twoLayerFormIndex B) :
    generalBidegreeFormMonomial 1 B p ab = twoLayerFormMonomial B p ab := by
  simp only [generalBidegreeFormMonomial, twoLayerFormMonomial]
  rw [generalBidegreeFormSource_one_eq_twoLayerFormSource,
    generalBidegreeFormTarget_eq_twoLayerFormTarget]

/-- The general `(1,B)` homogeneous form evaluation equals the two-layer
form evaluation for the same coefficient vector and point. -/
theorem generalBidegreeFormEval_one_eq_twoLayerFormEval
    (B : ℕ) (c : twoLayerFormIndex B → ℤ) (p : TwoLayerFormPoint) :
    generalBidegreeFormEval 1 B c p = twoLayerFormEval B c p := by
  simp only [generalBidegreeFormEval, twoLayerFormEval]
  apply Finset.sum_congr rfl
  intro ab _
  rw [generalBidegreeFormMonomial_one_eq_twoLayerFormMonomial]

/-- The general `(1,B)` evaluation matrix is exactly the two-layer evaluation
matrix, with no row or column rescaling. -/
theorem generalBidegreeFormEvaluationMatrix_one_eq_twoLayerFormEvaluationMatrix
    {ι : Type*} (B : ℕ) (points : ι → TwoLayerFormPoint) :
    generalBidegreeFormEvaluationMatrix 1 B points =
      twoLayerFormEvaluationMatrix B points := by
  ext r ab
  exact generalBidegreeFormMonomial_one_eq_twoLayerFormMonomial B (points r) ab

end PellPaper
