import Pell.IntegralAuxiliaryRelation
import Pell.GeneralBidegreeAuxiliaryRelation

/-!
# Entrywise bounds for integral bidegree evaluation matrices

The auxiliary-height argument in `L:quantitative-two-layer-height` of
`main.tex` begins with an elementary fact: at a row whose source homogeneous
coordinates have absolute value at most `S` and whose target homogeneous
coordinates have absolute value at most `T`, every integral bidegree-`(1,B)`
evaluation entry has absolute value at most `S * T^B`.

This file proves that fact for the project's literal two-layer definitions,
and its general bidegree `(A,B)` analogue used by `L:sheared`.  These are only
entrywise bounds.  They do not select a maximal minor, compare coefficient
heights, bound a determinant, or count points.
-/

namespace PellPaper

/-- A pair of integral homogeneous source and target coordinates is bounded
by `S` and `T`, respectively, in absolute value. -/
def twoLayerFormPointCoordinatesBounded (S T : ℤ) (p : TwoLayerFormPoint) : Prop :=
  |p.1.1| ≤ S ∧ |p.1.2| ≤ S ∧ |p.2.1| ≤ T ∧ |p.2.2| ≤ T

/-- The same coordinate-bound predicate, named for the general bidegree
evaluation matrix.  The point type is definitionally the same as the
two-layer point type, but retaining this name keeps the two uses explicit. -/
def generalBidegreeFormPointCoordinatesBounded (S T : ℤ)
    (p : GeneralBidegreeFormPoint) : Prop :=
  |p.1.1| ≤ S ∧ |p.1.2| ≤ S ∧ |p.2.1| ≤ T ∧ |p.2.2| ≤ T

/-- A homogeneous binary monomial of degree `n` is bounded by `K^n` when
both integral coordinates have absolute value at most nonnegative `K`. -/
theorem abs_homogeneousBinaryMonomial_le_pow
    (n : ℕ) (z : ℤ × ℤ) (i : Fin (n + 1)) {K : ℤ}
    (hK : 0 ≤ K) (hz₁ : |z.1| ≤ K) (hz₂ : |z.2| ≤ K) :
    |z.1 ^ (n - i.1) * z.2 ^ i.1| ≤ K ^ n := by
  rw [abs_mul, abs_pow, abs_pow]
  have hi : i.1 ≤ n := Nat.le_of_lt_succ i.2
  calc
    |z.1| ^ (n - i.1) * |z.2| ^ i.1 ≤
        K ^ (n - i.1) * K ^ i.1 := by
      exact mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg z.1) hz₁ _)
        (pow_le_pow_left₀ (abs_nonneg z.2) hz₂ _)
        (Int.pow_nonneg (abs_nonneg z.2))
        (Int.pow_nonneg hK)
    _ = K ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hi]

/-- A degree-`B` target monomial in the actual two-layer evaluation matrix
has the expected `T^B` absolute-value bound. -/
theorem abs_twoLayerFormTarget_le_pow
    (B : ℕ) (y : ℤ × ℤ) (b : Fin (B + 1)) {T : ℤ}
    (hT : 0 ≤ T) (hy₁ : |y.1| ≤ T) (hy₂ : |y.2| ≤ T) :
    |twoLayerFormTarget B y b| ≤ T ^ B := by
  simpa [twoLayerFormTarget] using
    abs_homogeneousBinaryMonomial_le_pow B y b hT hy₁ hy₂

/-- A degree-one source coordinate in the actual two-layer evaluation matrix
is bounded by the common source-coordinate bound. -/
theorem abs_twoLayerFormSource_le
    (x : ℤ × ℤ) (a : Fin 2) {S : ℤ}
    (hx₁ : |x.1| ≤ S) (hx₂ : |x.2| ≤ S) :
    |twoLayerFormSource x a| ≤ S := by
  by_cases ha : a = 0
  · subst a
    simpa [twoLayerFormSource] using hx₁
  · simpa [twoLayerFormSource, ha] using hx₂

/-- Every raw integral bidegree-`(1,B)` evaluation entry is bounded by
`S * T^B` under the source/target coordinate bounds in the paper. -/
theorem abs_twoLayerFormMonomial_le_source_mul_target_pow
    (B : ℕ) (p : TwoLayerFormPoint) (ab : twoLayerFormIndex B) {S T : ℤ}
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hcoords : twoLayerFormPointCoordinatesBounded S T p) :
    |twoLayerFormMonomial B p ab| ≤ S * T ^ B := by
  rw [twoLayerFormMonomial, abs_mul]
  exact mul_le_mul
    (abs_twoLayerFormSource_le p.1 ab.1 hcoords.1 hcoords.2.1)
    (abs_twoLayerFormTarget_le_pow B p.2 ab.2 hT hcoords.2.2.1 hcoords.2.2.2)
    (abs_nonneg (twoLayerFormTarget B p.2 ab.2)) hS

/-- The literal entry of the project's two-layer integral evaluation matrix
has the `S * T^B` bound on every row satisfying the coordinate hypotheses. -/
theorem abs_twoLayerFormEvaluationMatrix_apply_le_source_mul_target_pow
    {ι : Type*} (B : ℕ) (points : ι → TwoLayerFormPoint) {S T : ℤ}
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ r, twoLayerFormPointCoordinatesBounded S T (points r))
    (r : ι) (ab : twoLayerFormIndex B) :
    |twoLayerFormEvaluationMatrix B points r ab| ≤ S * T ^ B := by
  exact abs_twoLayerFormMonomial_le_source_mul_target_pow B (points r) ab hS hT
    (hpoints r)

/-- With one common coordinate bound `K`, a two-layer entry is bounded by
`K^(B+1)`.  This is the uniform form directly consumable by the factorial
cofactor bound. -/
theorem abs_twoLayerFormMonomial_le_pow_succ
    (B : ℕ) (p : TwoLayerFormPoint) (ab : twoLayerFormIndex B) {K : ℤ}
    (hK : 0 ≤ K) (hcoords : twoLayerFormPointCoordinatesBounded K K p) :
    |twoLayerFormMonomial B p ab| ≤ K ^ (B + 1) := by
  have h := abs_twoLayerFormMonomial_le_source_mul_target_pow B p ab hK hK hcoords
  simpa [pow_succ, mul_comm] using h

/-- A uniform entry bound for the literal two-layer evaluation matrix.  Its
conclusion has exactly the pointwise shape required as the `hM` hypothesis of
`abs_cofactorKernelVector_le_factorial_mul_pow`. -/
theorem abs_twoLayerFormEvaluationMatrix_apply_le_pow_succ
    {ι : Type*} (B : ℕ) (points : ι → TwoLayerFormPoint) {K : ℤ}
    (hK : 0 ≤ K)
    (hpoints : ∀ r, twoLayerFormPointCoordinatesBounded K K (points r))
    (r : ι) (ab : twoLayerFormIndex B) :
    |twoLayerFormEvaluationMatrix B points r ab| ≤ K ^ (B + 1) := by
  exact abs_twoLayerFormMonomial_le_pow_succ B (points r) ab hK (hpoints r)

/-- A degree-`A` source monomial in the standard general-bidegree matrix has
the `S^A` bound. -/
theorem abs_generalBidegreeFormSource_le_pow
    (A : ℕ) (x : ℤ × ℤ) (a : Fin (A + 1)) {S : ℤ}
    (hS : 0 ≤ S) (hx₁ : |x.1| ≤ S) (hx₂ : |x.2| ≤ S) :
    |generalBidegreeFormSource A x a| ≤ S ^ A := by
  simpa [generalBidegreeFormSource] using
    abs_homogeneousBinaryMonomial_le_pow A x a hS hx₁ hx₂

/-- A degree-`B` target monomial in the standard general-bidegree matrix has
the `T^B` bound. -/
theorem abs_generalBidegreeFormTarget_le_pow
    (B : ℕ) (y : ℤ × ℤ) (b : Fin (B + 1)) {T : ℤ}
    (hT : 0 ≤ T) (hy₁ : |y.1| ≤ T) (hy₂ : |y.2| ≤ T) :
    |generalBidegreeFormTarget B y b| ≤ T ^ B := by
  simpa [generalBidegreeFormTarget] using
    abs_homogeneousBinaryMonomial_le_pow B y b hT hy₁ hy₂

/-- Every raw integral standard bidegree-`(A,B)` evaluation entry is bounded
by `S^A * T^B` under separate source and target coordinate bounds. -/
theorem abs_generalBidegreeFormMonomial_le_source_pow_mul_target_pow
    (A B : ℕ) (p : GeneralBidegreeFormPoint)
    (ab : generalBidegreeFormIndex A B) {S T : ℤ}
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hcoords : generalBidegreeFormPointCoordinatesBounded S T p) :
    |generalBidegreeFormMonomial A B p ab| ≤ S ^ A * T ^ B := by
  rw [generalBidegreeFormMonomial, abs_mul]
  exact mul_le_mul
    (abs_generalBidegreeFormSource_le_pow A p.1 ab.1 hS hcoords.1 hcoords.2.1)
    (abs_generalBidegreeFormTarget_le_pow B p.2 ab.2 hT hcoords.2.2.1 hcoords.2.2.2)
    (abs_nonneg (generalBidegreeFormTarget B p.2 ab.2)) (Int.pow_nonneg hS)

/-- The literal entry of the project's standard general-bidegree evaluation
matrix has the `S^A * T^B` bound on every bounded row. -/
theorem abs_generalBidegreeFormEvaluationMatrix_apply_le_source_pow_mul_target_pow
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint) {S T : ℤ}
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ r, generalBidegreeFormPointCoordinatesBounded S T (points r))
    (r : ι) (ab : generalBidegreeFormIndex A B) :
    |generalBidegreeFormEvaluationMatrix A B points r ab| ≤ S ^ A * T ^ B := by
  exact abs_generalBidegreeFormMonomial_le_source_pow_mul_target_pow A B (points r)
    ab hS hT (hpoints r)

/-- A uniform entry bound for the standard general-bidegree evaluation
matrix.  It is a direct common-bound interface for a cofactor construction. -/
theorem abs_generalBidegreeFormEvaluationMatrix_apply_le_pow_add
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint) {K : ℤ}
    (hK : 0 ≤ K)
    (hpoints : ∀ r, generalBidegreeFormPointCoordinatesBounded K K (points r))
    (r : ι) (ab : generalBidegreeFormIndex A B) :
    |generalBidegreeFormEvaluationMatrix A B points r ab| ≤ K ^ (A + B) := by
  have h := abs_generalBidegreeFormMonomial_le_source_pow_mul_target_pow A B
    (points r) ab hK hK (hpoints r)
  simpa [generalBidegreeFormEvaluationMatrix, ← pow_add] using h

end PellPaper
