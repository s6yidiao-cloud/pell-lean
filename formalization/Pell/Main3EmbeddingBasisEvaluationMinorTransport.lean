import Pell.Main3EmbeddingBasisColumnChangeDeterminant
import Pell.ShearedIntegralMinorTransport
import Mathlib.Tactic

/-!
# Evaluation-minor transport to the quadratic embedding basis

This module connects the explicit embedding-basis column-change determinant
to the project's literal integral bidegree-`(1,B)` evaluation matrix.

The main algebraic input is an all-degree binomial action identity for
`binarySymmetricPowerTwoPointMatrix`.  It identifies right multiplication of
the standard monomial row by the two-point matrix with evaluation at the two
linear forms.  The bidegree identity then factors into independent source and
target identities.

For every finite row family and every injection selecting a full square
minor, the transformed embedding minor is the complex cast of the selected
integral minor times the common column-change matrix.  Determinant
multiplicativity and the canonical discriminant factor give an exact division
formula, and hence the desired absolute-value bound.

No centre extraction, radial normalization, localization estimate,
determinant decay, or point/cell count is asserted here.
-/

namespace PellPaper

open scoped BigOperators Kronecker

noncomputable section

/-- The standard ordered degree-`B` binary monomial row
`X^(B-i) Y^i`. -/
def binaryHomogeneousMonomial
    {R : Type*} [CommRing R] (B : ℕ) (x y : R) (i : Fin (B + 1)) : R :=
  x ^ (B - i.1) * y ^ i.1

/-- The degree-zero endpoint of the explicit symmetric-power matrix. -/
theorem binarySymmetricPowerTwoPointMatrix_zero
    {R : Type*} [CommRing R] (u v : R) :
    binarySymmetricPowerTwoPointMatrix 0 u v = !![1] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [binarySymmetricPowerTwoPointMatrix,
    binarySymmetricPowerTranslationMatrix,
    binarySymmetricPowerShearDilationMatrix, Matrix.mul_apply]

/-- The degree-two endpoint explicitly displays the coefficient columns of
`(X+uY)^(2-j)(X+vY)^j`.  Together with the canonical degree-one theorem,
this fixes the low-degree conventions `B=0,1,2`. -/
theorem binarySymmetricPowerTwoPointMatrix_two
    {R : Type*} [CommRing R] (u v : R) :
    binarySymmetricPowerTwoPointMatrix 2 u v =
      !![1, 1, 1;
         2 * u, u + v, 2 * v;
         u ^ 2, u * v, v ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binarySymmetricPowerTwoPointMatrix,
      binarySymmetricPowerTranslationMatrix,
      binarySymmetricPowerShearDilationMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Right multiplication by the shear-dilation factor replaces the second
linear form `Y` by `X+dY`, while retaining the first factor `X`. -/
theorem sum_binaryHomogeneousMonomial_mul_shearDilation
    {R : Type*} [CommRing R]
    (B : ℕ) (x y d : R) (j : Fin (B + 1)) :
    ∑ i : Fin (B + 1),
        binaryHomogeneousMonomial B x y i *
          binarySymmetricPowerShearDilationMatrix B d i j =
      x ^ (B - j.1) * (x + d * y) ^ j.1 := by
  classical
  let f : ℕ → R := fun i =>
    x ^ (B - i) * y ^ i *
      (if i ≤ j.1 then (Nat.choose j.1 i : R) * d ^ i else 0)
  calc
    (∑ i : Fin (B + 1),
        binaryHomogeneousMonomial B x y i *
          binarySymmetricPowerShearDilationMatrix B d i j) =
        ∑ i ∈ Finset.range (B + 1), f i := by
      simpa [f, binaryHomogeneousMonomial,
        binarySymmetricPowerShearDilationMatrix] using
        (Fin.sum_univ_eq_sum_range f (B + 1))
    _ = ∑ i ∈ Finset.range (j.1 + 1), f i := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro i hiB hij
        simp only [Finset.mem_range] at hiB hij
        simp [f]
        omega
    _ = x ^ (B - j.1) *
        ∑ i ∈ Finset.range (j.1 + 1),
          (d * y) ^ i * x ^ (j.1 - i) * (Nat.choose j.1 i : R) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [f, show i ≤ j.1 by omega, ↓reduceIte]
      rw [show B - i = (B - j.1) + (j.1 - i) by omega, pow_add,
        mul_pow]
      ring
    _ = x ^ (B - j.1) * (x + d * y) ^ j.1 := by
      congr 1
      simpa [add_comm] using (add_pow (d * y) x j.1).symm

/-- Right multiplication by the translation factor replaces `X` by
`X+uY` in the standard homogeneous monomial row. -/
theorem sum_binaryHomogeneousMonomial_mul_translation
    {R : Type*} [CommRing R]
    (B : ℕ) (x y u : R) (j : Fin (B + 1)) :
    ∑ i : Fin (B + 1),
        binaryHomogeneousMonomial B x y i *
          binarySymmetricPowerTranslationMatrix B u i j =
      (x + u * y) ^ (B - j.1) * y ^ j.1 := by
  classical
  let f : ℕ → R := fun i =>
    x ^ (B - i) * y ^ i *
      (if j.1 ≤ i then
        (Nat.choose (B - j.1) (i - j.1) : R) * u ^ (i - j.1)
      else 0)
  have hjB : j.1 ≤ B := Nat.le_of_lt_succ j.2
  calc
    (∑ i : Fin (B + 1),
        binaryHomogeneousMonomial B x y i *
          binarySymmetricPowerTranslationMatrix B u i j) =
        ∑ i ∈ Finset.range (B + 1), f i := by
      simpa [f, binaryHomogeneousMonomial,
        binarySymmetricPowerTranslationMatrix] using
        (Fin.sum_univ_eq_sum_range f (B + 1))
    _ = ∑ r ∈ Finset.range (B - j.1 + 1), f (j.1 + r) := by
      have hsplit := Finset.sum_range_add f j.1 (B + 1 - j.1)
      rw [show j.1 + (B + 1 - j.1) = B + 1 by omega] at hsplit
      rw [hsplit]
      have hzero : ∑ i ∈ Finset.range j.1, f i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [f, show ¬j.1 ≤ i by omega]
      rw [hzero, zero_add]
      rw [show B + 1 - j.1 = B - j.1 + 1 by omega]
    _ = (∑ r ∈ Finset.range (B - j.1 + 1),
        (u * y) ^ r * x ^ (B - j.1 - r) *
          (Nat.choose (B - j.1) r : R)) * y ^ j.1 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_range] at hr
      simp only [f]
      rw [if_pos (by omega)]
      rw [show B - (j.1 + r) = B - j.1 - r by omega,
        show j.1 + r - j.1 = r by omega, pow_add, mul_pow]
      ring
    _ = (x + u * y) ^ (B - j.1) * y ^ j.1 := by
      congr 1
      simpa [add_comm] using (add_pow (u * y) x (B - j.1)).symm

/-- All-degree action identity for the explicit two-point symmetric-power
matrix: its `j`th output is the homogeneous monomial in the two linear forms
`X+uY` and `X+vY`. -/
theorem sum_binaryHomogeneousMonomial_mul_twoPointMatrix
    {R : Type*} [CommRing R]
    (B : ℕ) (x y u v : R) (j : Fin (B + 1)) :
    ∑ i : Fin (B + 1),
        binaryHomogeneousMonomial B x y i *
          binarySymmetricPowerTwoPointMatrix B u v i j =
      (x + u * y) ^ (B - j.1) * (x + v * y) ^ j.1 := by
  classical
  let row : Matrix (Fin 1) (Fin (B + 1)) R :=
    fun _ i => binaryHomogeneousMonomial B x y i
  let translated : Matrix (Fin 1) (Fin (B + 1)) R :=
    fun _ i => (x + u * y) ^ (B - i.1) * y ^ i.1
  have htranslation :
      row * binarySymmetricPowerTranslationMatrix B u = translated := by
    ext i k
    simp only [row, translated]
    exact sum_binaryHomogeneousMonomial_mul_translation B x y u k
  calc
    (∑ i : Fin (B + 1),
        binaryHomogeneousMonomial B x y i *
          binarySymmetricPowerTwoPointMatrix B u v i j) =
        (row * binarySymmetricPowerTwoPointMatrix B u v) 0 j := by
      rfl
    _ = ((row * binarySymmetricPowerTranslationMatrix B u) *
        binarySymmetricPowerShearDilationMatrix B (v - u)) 0 j := by
      rw [binarySymmetricPowerTwoPointMatrix, Matrix.mul_assoc]
    _ = (translated *
        binarySymmetricPowerShearDilationMatrix B (v - u)) 0 j := by
      rw [htranslation]
    _ = (x + u * y) ^ (B - j.1) *
        ((x + u * y) + (v - u) * y) ^ j.1 := by
      simp only [translated]
      exact sum_binaryHomogeneousMonomial_mul_shearDilation
        B (x + u * y) y (v - u) j
    _ = (x + u * y) ^ (B - j.1) * (x + v * y) ^ j.1 := by
      congr 2
      ring

/-- The standard bidegree-`(1,B)` monomial over a commutative ring, in the
same exponent-of-second-coordinate convention as
`generalBidegreeFormMonomial`. -/
def bidegreeOneHomogeneousMonomial
    {R : Type*} [CommRing R]
    (B : ℕ) (x0 x1 y0 y1 : R) (ab : generalBidegreeFormIndex 1 B) : R :=
  x0 ^ (1 - ab.1.1) * x1 ^ ab.1.1 *
    (y0 ^ (B - ab.2.1) * y1 ^ ab.2.1)

/-- The unreflected embedding-basis monomial produced by the explicit common
column change.  Its source forms are `(alpha, starAlpha)` and its target forms
are `(starGamma, gamma)`. -/
def bidegreeOneEmbeddingBasisMonomial
    {R : Type*} [CommRing R]
    (B : ℕ) (omega omegaBar x0 x1 y0 y1 : R)
    (ij : generalBidegreeFormIndex 1 B) : R :=
  (x0 + omega * x1) ^ (1 - ij.1.1) *
    (x0 + omegaBar * x1) ^ ij.1.1 *
    ((y0 + omegaBar * y1) ^ (B - ij.2.1) *
      (y0 + omega * y1) ^ ij.2.1)

/-- The all-`B` bidegree row action.  It is the product of the degree-one
source action and the degree-`B` target action. -/
theorem sum_bidegreeOneHomogeneousMonomial_mul_columnChange
    {R : Type*} [CommRing R]
    (B : ℕ) (omega omegaBar x0 x1 y0 y1 : R)
    (ij : generalBidegreeFormIndex 1 B) :
    ∑ ab : generalBidegreeFormIndex 1 B,
        bidegreeOneHomogeneousMonomial B x0 x1 y0 y1 ab *
          (((quadraticEmbeddingBasisMatrix omega omegaBar).transpose ⊗ₖ
            binarySymmetricPowerTwoPointMatrix B omegaBar omega) ab ij) =
      bidegreeOneEmbeddingBasisMonomial
        B omega omegaBar x0 x1 y0 y1 ij := by
  classical
  rw [show (quadraticEmbeddingBasisMatrix omega omegaBar).transpose =
      binarySymmetricPowerTwoPointMatrix 1 omega omegaBar by
    exact (binarySymmetricPowerTwoPointMatrix_one omega omegaBar).symm]
  simp only [Matrix.kroneckerMap_apply, bidegreeOneHomogeneousMonomial]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [show ∀ (a : Fin 2) (b : Fin (B + 1)),
      x0 ^ (1 - a.1) * x1 ^ a.1 *
          (y0 ^ (B - b.1) * y1 ^ b.1) *
          (binarySymmetricPowerTwoPointMatrix 1 omega omegaBar a ij.1 *
            binarySymmetricPowerTwoPointMatrix B omegaBar omega b ij.2) =
        (binaryHomogeneousMonomial 1 x0 x1 a *
          binarySymmetricPowerTwoPointMatrix 1 omega omegaBar a ij.1) *
        (binaryHomogeneousMonomial B y0 y1 b *
          binarySymmetricPowerTwoPointMatrix B omegaBar omega b ij.2) by
    intro a b
    simp only [binaryHomogeneousMonomial]
    ring]
  rw [← Fintype.sum_mul_sum,
    sum_binaryHomogeneousMonomial_mul_twoPointMatrix,
    sum_binaryHomogeneousMonomial_mul_twoPointMatrix]
  rfl

/-- The complex embedding-basis evaluation matrix attached to a literal
family of integral homogeneous source-target points. -/
def main3EmbeddingBasisEvaluationMatrix
    {ι : Type*} (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex 1 B) ℂ :=
  fun r ij =>
    bidegreeOneEmbeddingBasisMonomial B omega omegaBar
      (points r).1.1 (points r).1.2 (points r).2.1 (points r).2.2 ij

/-- Right multiplication of the actual integral evaluation matrix, after
complex casting, is exactly the embedding-basis evaluation matrix. -/
theorem map_generalBidegreeEvaluation_mul_embeddingBasisColumnChange
    {ι : Type*} (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint) :
    (generalBidegreeFormEvaluationMatrix 1 B points).map
        (Int.castRingHom ℂ) *
      main3EmbeddingBasisColumnChangeMatrix B omega omegaBar =
        main3EmbeddingBasisEvaluationMatrix B omega omegaBar points := by
  ext r ij
  simpa [Matrix.mul_apply, generalBidegreeFormEvaluationMatrix,
    generalBidegreeFormMonomial, generalBidegreeFormSource,
    generalBidegreeFormTarget, bidegreeOneHomogeneousMonomial,
    main3EmbeddingBasisEvaluationMatrix,
    main3EmbeddingBasisColumnChangeMatrix] using
    (sum_bidegreeOneHomogeneousMonomial_mul_columnChange
      (R := ℂ) B omega omegaBar
      ((points r).1.1 : ℂ) ((points r).1.2 : ℂ)
      ((points r).2.1 : ℂ) ((points r).2.2 : ℂ) ij)

/-- The manuscript-oriented column order is obtained by reflecting both
bounded monomial indices. -/
def main3ReflectedEmbeddingBasisEvaluationMatrix
    {ι : Type*} (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex 1 B) ℂ :=
  (main3EmbeddingBasisEvaluationMatrix B omega omegaBar points).submatrix id
    (generalBidegreeFormIndexReflection 1 B)

/-- Entry formula after reflection: source columns are
`starAlpha^(1-i) alpha^i`, while target columns are
`gamma^(B-j) starGamma^j`.  This is the exponent orientation used by the
normalized manuscript display. -/
theorem main3ReflectedEmbeddingBasisEvaluationMatrix_apply
    {ι : Type*} (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (r : ι) (ij : generalBidegreeFormIndex 1 B) :
    main3ReflectedEmbeddingBasisEvaluationMatrix
        B omega omegaBar points r ij =
      ((points r).1.1 + omega * (points r).1.2) ^ ij.1.1 *
        ((points r).1.1 + omegaBar * (points r).1.2) ^ (1 - ij.1.1) *
        (((points r).2.1 + omegaBar * (points r).2.2) ^ ij.2.1 *
          ((points r).2.1 + omega * (points r).2.2) ^ (B - ij.2.1)) := by
  simp only [main3ReflectedEmbeddingBasisEvaluationMatrix,
    Matrix.submatrix_apply, id_eq, main3EmbeddingBasisEvaluationMatrix,
    bidegreeOneEmbeddingBasisMonomial]
  rw [sourceExponent_sub_indexReflection_eq,
    indexReflection_sourceExponent_eq_sub,
    targetExponent_sub_indexReflection_eq,
    indexReflection_targetExponent_eq_sub]

/-- Every selected transformed square matrix is the cast of the selected
integral evaluation minor times the same common column-change matrix. -/
theorem main3EmbeddingBasisEvaluationMatrix_selected_eq_castMinor_mul
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    (main3EmbeddingBasisEvaluationMatrix
        B omega omegaBar points).submatrix s id =
      ((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).map
          (Int.castRingHom ℂ) *
        main3EmbeddingBasisColumnChangeMatrix B omega omegaBar := by
  rw [← map_generalBidegreeEvaluation_mul_embeddingBasisColumnChange]
  simpa only [Matrix.submatrix_map, Matrix.submatrix_id_id] using
    (Matrix.submatrix_mul
      ((generalBidegreeFormEvaluationMatrix 1 B points).map (Int.castRingHom ℂ))
      (main3EmbeddingBasisColumnChangeMatrix B omega omegaBar)
      s id id Function.bijective_id)

/-- Determinant of a selected embedding-basis minor equals the integral
minor, cast to `ℂ`, times the exact common column-change determinant. -/
theorem det_main3EmbeddingBasisEvaluationMatrix_selected
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ((main3EmbeddingBasisEvaluationMatrix
        B omega omegaBar points).submatrix s id).det =
      (((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℂ) *
        (main3EmbeddingBasisColumnChangeMatrix B omega omegaBar).det := by
  rw [main3EmbeddingBasisEvaluationMatrix_selected_eq_castMinor_mul,
    Matrix.det_mul]
  have hmap := RingHom.map_det (Int.castRingHom ℂ)
    ((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id)
  change
    (((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℂ) =
      (((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).map
        (Int.castRingHom ℂ)).det at hmap
  rw [← hmap]

/-- Reflecting the embedding columns changes only the determinant
orientation, not its complex norm. -/
theorem norm_det_main3ReflectedEmbeddingBasisEvaluationMatrix_selected
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ‖((main3ReflectedEmbeddingBasisEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ =
      ‖((main3EmbeddingBasisEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ := by
  have hsub :
      (main3ReflectedEmbeddingBasisEvaluationMatrix
          B omega omegaBar points).submatrix s id =
        ((main3EmbeddingBasisEvaluationMatrix
          B omega omegaBar points).submatrix s id).submatrix
            id (generalBidegreeFormIndexReflection 1 B) := by
    rfl
  rw [hsub, Matrix.det_permute', norm_mul]
  rw [Complex.norm_intCast, abs_unit_intCast, one_mul]

local instance main3EmbeddingBasisEvaluationMinorTransport_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The embedding-basis evaluation matrix specialized to the fixed
shifted-square integral basis and an arbitrary field embedding. -/
def main3ShiftedSquareEmbeddingBasisEvaluationMatrix
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex 1 B) ℂ :=
  main3EmbeddingBasisEvaluationMatrix B
    (sigma F.omega) (sigma (star F.omega)) points

/-- The reflected, manuscript-oriented specialization of the embedding
evaluation matrix. -/
def main3ShiftedSquareReflectedEmbeddingBasisEvaluationMatrix
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex 1 B) ℂ :=
  main3ReflectedEmbeddingBasisEvaluationMatrix B
    (sigma F.omega) (sigma (star F.omega)) points

/-- Project-specialized selected-square-matrix product. -/
theorem main3ShiftedSquareEmbeddingBasisEvaluationMatrix_selected_eq_castMinor_mul
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    (main3ShiftedSquareEmbeddingBasisEvaluationMatrix
        B F sigma points).submatrix s id =
      ((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).map
          (Int.castRingHom ℂ) *
        main3ShiftedSquareEmbeddingBasisColumnChangeMatrix B F sigma := by
  simpa [main3ShiftedSquareEmbeddingBasisEvaluationMatrix,
    main3ShiftedSquareEmbeddingBasisColumnChangeMatrix] using
    (main3EmbeddingBasisEvaluationMatrix_selected_eq_castMinor_mul B
      (sigma F.omega) (sigma (star F.omega)) points s)

/-- The project-specialized selected-minor determinant identity. -/
theorem det_main3ShiftedSquareEmbeddingBasisEvaluationMatrix_selected
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ((main3ShiftedSquareEmbeddingBasisEvaluationMatrix
        B F sigma points).submatrix s id).det =
      (((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℂ) *
        (main3ShiftedSquareEmbeddingBasisColumnChangeMatrix B F sigma).det := by
  simpa [main3ShiftedSquareEmbeddingBasisEvaluationMatrix,
    main3ShiftedSquareEmbeddingBasisColumnChangeMatrix] using
    (det_main3EmbeddingBasisEvaluationMatrix_selected B
      (sigma F.omega) (sigma (star F.omega)) points s)

/-- The same selected-minor identity with the exact signed column-change
factor substituted. -/
theorem det_main3ShiftedSquareEmbeddingBasisEvaluationMatrix_selected_eq_exactFactor
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ((main3ShiftedSquareEmbeddingBasisEvaluationMatrix
        B F sigma points).submatrix s id).det =
      (((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℂ) *
        ((-1) ^ (B + 1) *
          (sigma F.omega - sigma (star F.omega)) ^ ((B + 1) ^ 2)) := by
  rw [det_main3ShiftedSquareEmbeddingBasisEvaluationMatrix_selected,
    main3ShiftedSquareEmbeddingBasisColumnChangeMatrix,
    det_main3EmbeddingBasisColumnChangeMatrix]

/-- The real discriminant factor in the final denominator is strictly
positive. -/
theorem main3ShiftedSquare_discriminantRpowFactor_pos
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) :
    0 < Real.rpow
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
      (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) := by
  have hdisc :
      (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero (rationalQuadraticAlgebra (-a))
  exact Real.rpow_pos_of_pos (abs_pos.mpr hdisc) _

/-- The common project column-change determinant is nonzero, derived from
the nonzero number-field discriminant. -/
theorem main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_det_ne_zero
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (main3ShiftedSquareEmbeddingBasisColumnChangeMatrix B F sigma).det ≠ 0 := by
  have hnorm :=
    norm_det_main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq_discr_rpow
      B F sigma
  apply (norm_ne_zero_iff).mp
  rw [hnorm]
  exact ne_of_gt (main3ShiftedSquare_discriminantRpowFactor_pos B)

/-- Exact complex division: the cast integral minor is the embedding minor
divided by the nonzero common column-change determinant. -/
theorem cast_det_generalBidegreeMinor_eq_embeddingBasis_det_div_changeDet
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    (((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℂ) =
      ((main3ShiftedSquareEmbeddingBasisEvaluationMatrix
          B F sigma points).submatrix s id).det /
        (main3ShiftedSquareEmbeddingBasisColumnChangeMatrix B F sigma).det := by
  apply (eq_div_iff
    (main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_det_ne_zero
      B F sigma)).2
  symm
  exact det_main3ShiftedSquareEmbeddingBasisEvaluationMatrix_selected
    B F sigma points s

/-- Exact real absolute-value division by the manuscript discriminant
factor.  This is the quantitative interface needed for a later analytic
bound on the embedding minor. -/
theorem abs_cast_det_generalBidegreeMinor_eq_norm_embeddingBasis_det_div_discrRpow
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    |(((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℝ)| =
      ‖((main3ShiftedSquareEmbeddingBasisEvaluationMatrix
          B F sigma points).submatrix s id).det‖ /
        Real.rpow
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) := by
  have h := congrArg norm
    (cast_det_generalBidegreeMinor_eq_embeddingBasis_det_div_changeDet
      B F sigma points s)
  rw [norm_div,
    norm_det_main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq_discr_rpow]
    at h
  simpa only [Complex.norm_intCast] using h

/-- The bound form of the exact division identity. -/
theorem abs_cast_det_generalBidegreeMinor_le_norm_embeddingBasis_det_div_discrRpow
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    |(((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℝ)| ≤
      ‖((main3ShiftedSquareEmbeddingBasisEvaluationMatrix
          B F sigma points).submatrix s id).det‖ /
        Real.rpow
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) :=
  le_of_eq
    (abs_cast_det_generalBidegreeMinor_eq_norm_embeddingBasis_det_div_discrRpow
      B F sigma points s)

/-- The same exact norm-division formula in the reflected column order used
by the manuscript's normalized powers. -/
theorem abs_cast_det_generalBidegreeMinor_eq_norm_reflectedEmbeddingBasis_det_div_discrRpow
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    |(((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℝ)| =
      ‖((main3ShiftedSquareReflectedEmbeddingBasisEvaluationMatrix
          B F sigma points).submatrix s id).det‖ /
        Real.rpow
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) := by
  rw [
    abs_cast_det_generalBidegreeMinor_eq_norm_embeddingBasis_det_div_discrRpow
      B F sigma points s]
  congr 1
  exact
    (norm_det_main3ReflectedEmbeddingBasisEvaluationMatrix_selected B
      (sigma F.omega) (sigma (star F.omega)) points s).symm

/-- The reflected manuscript-oriented bound form. -/
theorem abs_cast_det_generalBidegreeMinor_le_norm_reflectedEmbeddingBasis_det_div_discrRpow
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    |(((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℝ)| ≤
      ‖((main3ShiftedSquareReflectedEmbeddingBasisEvaluationMatrix
          B F sigma points).submatrix s id).det‖ /
        Real.rpow
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) :=
  le_of_eq
    (abs_cast_det_generalBidegreeMinor_eq_norm_reflectedEmbeddingBasis_det_div_discrRpow
      B F sigma points s)

end

end PellPaper
