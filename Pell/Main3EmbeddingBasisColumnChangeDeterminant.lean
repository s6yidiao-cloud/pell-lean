import Pell.Main3ShiftedSquareRawCoordinateBounds
import Pell.ShiftedSquareFixedBasisNormalizedCoordinates
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# The embedding-basis column-change determinant in bidegree `(1,B)`

This module isolates the exact determinant factor in the embedding-basis
change used in `main3`.  For a two-row matrix

`[[1,u],[1,v]] = [[1,0],[1,v-u]] * [[1,u],[0,1]]`,

its degree-`B` binary symmetric-power coefficient matrix is represented by
the corresponding product of an explicit translation matrix and an explicit
shear-dilation matrix.  Their determinants are respectively `1` and
`(v-u)^(B*(B+1)/2)`.

Kronecker's determinant formula then gives the bidegree-`(1,B)` exponent
`(B+1)^2`.  The final theorem specializes `u,v` to the two embedded values of
an integral-basis generator and converts the generator difference to the
absolute field discriminant.

The project's native coefficient index records the exponent of the second
homogeneous coordinate.  With that index, the matrix below gives the inverse
of the normalized exponent orientation displayed in manuscript lines
1324--1326;
reflecting `(i,j)` to `(1-i,B-j)` recovers that display.  This permutation
does not change the determinant modulus proved here.  No normalized-row
entry formula is asserted in this module.

No determinant size estimate, minor comparison, or integrality assertion is
made here.
-/

namespace PellPaper

open scoped BigOperators Kronecker

noncomputable section

/-- The symmetric-power coefficient matrix for the translation
`(X,Y) |-> (X + uY,Y)` on binary forms of degree `B`. -/
def binarySymmetricPowerTranslationMatrix
    {R : Type*} [CommRing R] (B : ℕ) (u : R) :
    Matrix (Fin (B + 1)) (Fin (B + 1)) R :=
  fun i j =>
    if j.1 ≤ i.1 then
      (Nat.choose (B - j.1) (i.1 - j.1) : R) * u ^ (i.1 - j.1)
    else 0

/-- The symmetric-power coefficient matrix for
`(X,Y) |-> (X,X + dY)` on binary forms of degree `B`. -/
def binarySymmetricPowerShearDilationMatrix
    {R : Type*} [CommRing R] (B : ℕ) (d : R) :
    Matrix (Fin (B + 1)) (Fin (B + 1)) R :=
  fun i j =>
    if i.1 ≤ j.1 then
      (Nat.choose j.1 i.1 : R) * d ^ i.1
    else 0

/-- The factored degree-`B` symmetric-power coefficient matrix of
`[[1,u],[1,v]]`.  The order is the one induced by applying
`[[1,u],[0,1]]` first and then `[[1,0],[1,v-u]]`. -/
def binarySymmetricPowerTwoPointMatrix
    {R : Type*} [CommRing R] (B : ℕ) (u v : R) :
    Matrix (Fin (B + 1)) (Fin (B + 1)) R :=
  binarySymmetricPowerTranslationMatrix B u *
    binarySymmetricPowerShearDilationMatrix B (v - u)

private theorem binarySymmetricPowerTranslationMatrix_isLowerTriangular
    {R : Type*} [CommRing R] (B : ℕ) (u : R) :
    (binarySymmetricPowerTranslationMatrix B u).IsLowerTriangular := by
  intro i j hij
  unfold binarySymmetricPowerTranslationMatrix
  split_ifs with hji
  · have hijVal : i.1 < j.1 := hij
    omega
  · rfl

/-- The translation factor is unipotent. -/
theorem det_binarySymmetricPowerTranslationMatrix
    {R : Type*} [CommRing R] (B : ℕ) (u : R) :
    (binarySymmetricPowerTranslationMatrix B u).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _
    (binarySymmetricPowerTranslationMatrix_isLowerTriangular B u)]
  simp [binarySymmetricPowerTranslationMatrix]

private theorem binarySymmetricPowerShearDilationMatrix_isUpperTriangular
    {R : Type*} [CommRing R] (B : ℕ) (d : R) :
    (binarySymmetricPowerShearDilationMatrix B d).IsUpperTriangular := by
  intro i j hji
  unfold binarySymmetricPowerShearDilationMatrix
  split_ifs with hij
  · have hjiVal : j.1 < i.1 := hji
    omega
  · rfl

private theorem sum_fin_val (B : ℕ) :
    (∑ i : Fin (B + 1), i.1) = B * (B + 1) / 2 := by
  calc
    (∑ i : Fin (B + 1), i.1) =
        ∑ i ∈ Finset.range (B + 1), i := by
      simpa using Fin.sum_univ_eq_sum_range (fun i => i) (B + 1)
    _ = (B + 1) * B / 2 := by
      rw [Finset.sum_range_id]
      simp
    _ = B * (B + 1) / 2 := by rw [Nat.mul_comm]

/-- The shear-dilation factor has the standard binary symmetric-power
determinant. -/
theorem det_binarySymmetricPowerShearDilationMatrix
    {R : Type*} [CommRing R] (B : ℕ) (d : R) :
    (binarySymmetricPowerShearDilationMatrix B d).det =
      d ^ (B * (B + 1) / 2) := by
  rw [Matrix.det_of_isUpperTriangular
    (binarySymmetricPowerShearDilationMatrix_isUpperTriangular B d)]
  simp only [binarySymmetricPowerShearDilationMatrix, le_refl, ↓reduceIte,
    Nat.choose_self, Nat.cast_one, one_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [sum_fin_val]

/-- Exact determinant of the degree-`B` symmetric-power coefficient matrix
of `[[1,u],[1,v]]`. -/
theorem det_binarySymmetricPowerTwoPointMatrix
    {R : Type*} [CommRing R] (B : ℕ) (u v : R) :
    (binarySymmetricPowerTwoPointMatrix B u v).det =
      (v - u) ^ (B * (B + 1) / 2) := by
  rw [binarySymmetricPowerTwoPointMatrix, Matrix.det_mul,
    det_binarySymmetricPowerTranslationMatrix,
    det_binarySymmetricPowerShearDilationMatrix, one_mul]

/-- The source embedding-basis matrix `L`. -/
def quadraticEmbeddingBasisMatrix
    {R : Type*} [CommRing R] (omega omegaBar : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, omega; 1, omegaBar]

/-- The target embedding-basis matrix `L'`, obtained by reversing the two
embedding rows of `L` (equivalently, by swapping `omega` and `omegaBar` in
the second column). -/
def quadraticConjugateEmbeddingBasisMatrix
    {R : Type*} [CommRing R] (omega omegaBar : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, omegaBar; 1, omega]

/-- At degree one, the explicit symmetric-power coefficient convention is
the transpose of the displayed two-row matrix.  This is the convention
needed for right multiplication of an evaluation matrix whose columns are
`X^(B-j)Y^j`. -/
theorem binarySymmetricPowerTwoPointMatrix_one
    {R : Type*} [CommRing R] (u v : R) :
    binarySymmetricPowerTwoPointMatrix 1 u v =
      (quadraticEmbeddingBasisMatrix u v).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binarySymmetricPowerTwoPointMatrix,
      binarySymmetricPowerTranslationMatrix,
      binarySymmetricPowerShearDilationMatrix,
      quadraticEmbeddingBasisMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- At degree one in the target/conjugate order, the explicit matrix is the
transpose of the manuscript's displayed `L'`. -/
theorem binarySymmetricPowerConjugateTwoPointMatrix_one
    {R : Type*} [CommRing R] (omega omegaBar : R) :
    binarySymmetricPowerTwoPointMatrix 1 omegaBar omega =
      (quadraticConjugateEmbeddingBasisMatrix omega omegaBar).transpose := by
  simpa [quadraticConjugateEmbeddingBasisMatrix,
    quadraticEmbeddingBasisMatrix] using
    (binarySymmetricPowerTwoPointMatrix_one omegaBar omega)

/-- The bidegree-`(1,B)` coefficient-column change on the project index type
`Fin 2 × Fin (B+1)`.  Both factors use the transpose convention forced by
right multiplication of row evaluations. -/
def main3EmbeddingBasisColumnChangeMatrix
    (B : ℕ) (omega omegaBar : ℂ) :
    Matrix (Fin 2 × Fin (B + 1)) (Fin 2 × Fin (B + 1)) ℂ :=
  (quadraticEmbeddingBasisMatrix omega omegaBar).transpose ⊗ₖ
    binarySymmetricPowerTwoPointMatrix B omegaBar omega

/-- The same change in the manuscript's displayed row-matrix convention:
literally `L tensor Sym^B(L')`. -/
def main3ManuscriptEmbeddingBasisColumnChangeMatrix
    (B : ℕ) (omega omegaBar : ℂ) :
    Matrix (Fin 2 × Fin (B + 1)) (Fin 2 × Fin (B + 1)) ℂ :=
  quadraticEmbeddingBasisMatrix omega omegaBar ⊗ₖ
    (binarySymmetricPowerTwoPointMatrix B omegaBar omega).transpose

/-- The project coefficient-column convention is the transpose of the
manuscript row convention. -/
theorem main3EmbeddingBasisColumnChangeMatrix_eq_manuscript_transpose
    (B : ℕ) (omega omegaBar : ℂ) :
    main3EmbeddingBasisColumnChangeMatrix B omega omegaBar =
      (main3ManuscriptEmbeddingBasisColumnChangeMatrix
        B omega omegaBar).transpose := by
  rfl

/-- Exact determinant, including the orientation sign, of the bidegree
embedding-basis column change. -/
theorem det_main3EmbeddingBasisColumnChangeMatrix
    (B : ℕ) (omega omegaBar : ℂ) :
    (main3EmbeddingBasisColumnChangeMatrix B omega omegaBar).det =
      (-1) ^ (B + 1) *
        (omega - omegaBar) ^ ((B + 1) ^ 2) := by
  have htwo : B * (B + 1) / 2 * 2 = B * (B + 1) :=
    Nat.div_mul_cancel (Nat.two_dvd_mul_add_one B)
  rw [main3EmbeddingBasisColumnChangeMatrix, Matrix.det_kronecker,
    det_binarySymmetricPowerTwoPointMatrix]
  simp only [Fintype.card_fin]
  rw [show (quadraticEmbeddingBasisMatrix omega omegaBar).transpose.det =
      -(omega - omegaBar) by
    rw [Matrix.det_transpose, quadraticEmbeddingBasisMatrix,
      Matrix.det_fin_two]
    simp]
  rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul, mul_assoc, ← pow_add, htwo]
  congr 2
  ring

/-- The orientation disappears after taking complex modulus. -/
theorem norm_det_main3EmbeddingBasisColumnChangeMatrix
    (B : ℕ) (omega omegaBar : ℂ) :
    ‖(main3EmbeddingBasisColumnChangeMatrix B omega omegaBar).det‖ =
      ‖omega - omegaBar‖ ^ ((B + 1) ^ 2) := by
  rw [det_main3EmbeddingBasisColumnChangeMatrix, norm_mul, norm_pow, norm_pow]
  norm_num

/-- Literal manuscript-row formulation of the same modulus identity. -/
theorem norm_det_main3ManuscriptEmbeddingBasisColumnChangeMatrix
    (B : ℕ) (omega omegaBar : ℂ) :
    ‖(main3ManuscriptEmbeddingBasisColumnChangeMatrix
        B omega omegaBar).det‖ =
      ‖omega - omegaBar‖ ^ ((B + 1) ^ 2) := by
  rw [← Matrix.det_transpose]
  rw [← main3EmbeddingBasisColumnChangeMatrix_eq_manuscript_transpose]
  exact norm_det_main3EmbeddingBasisColumnChangeMatrix B omega omegaBar

local instance main3EmbeddingBasisColumnChangeDeterminant_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Fixing the integral basis and an arbitrary field embedding gives the
actual project coefficient-column matrix.  Field conjugation is applied
before `sigma`; no compatibility with complex conjugation is assumed. -/
def main3ShiftedSquareEmbeddingBasisColumnChangeMatrix
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (degree : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    Matrix (Fin 2 × Fin (degree + 1)) (Fin 2 × Fin (degree + 1)) ℂ :=
  main3EmbeddingBasisColumnChangeMatrix degree
    (sigma (F.omega : rationalQuadraticAlgebra (-a)))
    (sigma (star (F.omega : rationalQuadraticAlgebra (-a))))

/-- The embedded difference of the fixed integral-basis generator has norm
square equal to the absolute field discriminant. -/
theorem shiftedSquareFixedBasis_embeddingDifference_norm_sq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma ((F.omega : rationalQuadraticAlgebra (-a)) -
        star (F.omega : rationalQuadraticAlgebra (-a)))‖ ^ 2 =
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  rw [← norm_pow, ← map_pow,
    shiftedSquare_displayedOmega_sub_star_sq_eq_fieldDiscr
      F.basis F.omega F.t F.c F.basis_zero F.basis_one F.omega_sq,
    map_intCast, Complex.norm_intCast]

/-- Project-specific determinant factor in the coefficient-column
convention, written without fractional powers. -/
theorem norm_det_main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq_sqrt_discr_pow
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (degree : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖(main3ShiftedSquareEmbeddingBasisColumnChangeMatrix
        degree F sigma).det‖ =
      (Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|) ^
          ((degree + 1) ^ 2) := by
  have hbase :
      ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
          sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ =
        Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
    calc
      ‖sigma (F.omega : rationalQuadraticAlgebra (-a)) -
          sigma (star (F.omega : rationalQuadraticAlgebra (-a)))‖ =
          ‖sigma ((F.omega : rationalQuadraticAlgebra (-a)) -
            star (F.omega : rationalQuadraticAlgebra (-a)))‖ := by
        rw [map_sub]
      _ = Real.sqrt
          (‖sigma ((F.omega : rationalQuadraticAlgebra (-a)) -
            star (F.omega : rationalQuadraticAlgebra (-a)))‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
        rw [shiftedSquareFixedBasis_embeddingDifference_norm_sq F sigma]
  rw [main3ShiftedSquareEmbeddingBasisColumnChangeMatrix,
    norm_det_main3EmbeddingBasisColumnChangeMatrix, hbase]

/-- Literal manuscript-row formulation of the fixed-basis discriminant
factor.  It is the transpose of the project coefficient-column convention. -/
theorem norm_det_main3ShiftedSquareManuscriptEmbeddingBasisColumnChangeMatrix_eq_sqrt_discr_pow
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (degree : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖(main3ManuscriptEmbeddingBasisColumnChangeMatrix degree
        (sigma (F.omega : rationalQuadraticAlgebra (-a)))
        (sigma (star (F.omega : rationalQuadraticAlgebra (-a))))).det‖ =
      (Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|) ^
          ((degree + 1) ^ 2) := by
  rw [norm_det_main3ManuscriptEmbeddingBasisColumnChangeMatrix]
  have hbase :=
    norm_det_main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq_sqrt_discr_pow
      degree F sigma
  rw [main3ShiftedSquareEmbeddingBasisColumnChangeMatrix,
    norm_det_main3EmbeddingBasisColumnChangeMatrix] at hbase
  exact hbase

/-- The manuscript's `D_a^((B+1)^2/2)` form.  The exponent is explicitly
real; in particular, no natural-number truncating division occurs. -/
theorem norm_det_main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq_discr_rpow
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (degree : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖(main3ShiftedSquareEmbeddingBasisColumnChangeMatrix
        degree F sigma).det‖ =
      Real.rpow
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
        (((((degree + 1) ^ 2 : ℕ) : ℝ)) / 2) := by
  rw [
    norm_det_main3ShiftedSquareEmbeddingBasisColumnChangeMatrix_eq_sqrt_discr_pow]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg
    (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ))]
  congr 1
  push_cast
  ring

end

end PellPaper
