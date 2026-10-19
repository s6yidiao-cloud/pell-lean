import Pell.QuadraticAlgebraTwoRealPositivity
import Pell.QuadraticFormIdealVectorNorm

/-!
# Elementary real height window for quadratic-form ideal vectors

For a nonnegative discriminant, this file evaluates the attached-ideal vector
`a*x - theta*y` at the two displayed real embeddings.  A deliberately loose,
always-positive majorant bounds both absolute values when the two integral
coordinates lie in a common box.  Their product is the signed norm
`a * Q(x,y)`, so a nonzero represented value gives the reciprocal lower bound
at the positive embedding.

This is only an elementary height-window interface.  It neither specializes
the coordinate box to the ranges in the manuscript nor makes an asymptotic claim.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formRealHeight_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- A simple common upper bound for both displayed real embeddings of a form
vector whose two coordinates have absolute value at most `X`.  The added one
makes the majorant strictly positive even when `X = 0`. -/
def formIdealVectorRealHeightMajorant
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (X : ℝ) : ℝ :=
  1 + (|(Q.a : ℝ)| + |(Q.b : ℝ)| + Real.sqrt (D : ℝ)) * X

/-- The attached-ideal vector at the positive displayed embedding. -/
theorem rationalQuadraticAlgebraRealEmbedding_formIdealVector
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (x y : ℤ) :
    rationalQuadraticAlgebraRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D) =
      (Q.a : ℝ) * x + ((Q.b : ℝ) - Real.sqrt (D : ℝ)) * y / 2 := by
  rw [coe_formIdealVector]
  simp [rationalQuadraticAlgebraRealEmbedding, Algebra.smul_def]
  ring

/-- The attached-ideal vector at the conjugate displayed embedding. -/
theorem rationalQuadraticAlgebraNegativeRealEmbedding_formIdealVector
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (x y : ℤ) :
    rationalQuadraticAlgebraNegativeRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D) =
      (Q.a : ℝ) * x + ((Q.b : ℝ) + Real.sqrt (D : ℝ)) * y / 2 := by
  rw [coe_formIdealVector]
  simp [rationalQuadraticAlgebraNegativeRealEmbedding, Algebra.smul_def]
  ring

/-- The common majorant is strictly positive on every nonnegative coordinate
radius. -/
theorem formIdealVectorRealHeightMajorant_pos
    (D : ℤ) (_hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    {X : ℝ} (hX : 0 ≤ X) :
    0 < formIdealVectorRealHeightMajorant D Q X := by
  unfold formIdealVectorRealHeightMajorant
  have hsqrt : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  positivity

private theorem abs_realEmbedding_formIdealVector_le_majorant_aux
    {a b s x y X : ℝ} (hX : 0 ≤ X)
    (hx : |x| ≤ X) (hy : |y| ≤ X) :
    |a * x + (b + s) * y / 2| ≤
      1 + (|a| + |b| + |s|) * X := by
  have haX : |a * x| ≤ |a| * X := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hbs : |b + s| ≤ |b| + |s| := abs_add_le _ _
  have hby : |(b + s) * y| ≤ (|b| + |s|) * X := by
    rw [abs_mul]
    exact mul_le_mul hbs hy (abs_nonneg _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hhalf : |(b + s) * y / 2| ≤ (|b| + |s|) * X := by
    calc
      |(b + s) * y / 2| = |(b + s) * y| / 2 := by norm_num [abs_div]
      _ ≤ ((|b| + |s|) * X) / 2 := by gcongr
      _ ≤ (|b| + |s|) * X := by
        have hnonneg : 0 ≤ (|b| + |s|) * X :=
          mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hX
        linarith
  calc
    |a * x + (b + s) * y / 2| ≤ |a * x| + |(b + s) * y / 2| :=
      abs_add_le _ _
    _ ≤ |a| * X + (|b| + |s|) * X := add_le_add haX hhalf
    _ ≤ 1 + (|a| + |b| + |s|) * X := by ring_nf; linarith

/-- Absolute-value upper bound at the positive displayed embedding. -/
theorem abs_rationalQuadraticAlgebraRealEmbedding_formIdealVector_le_majorant
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    {x y : ℤ} {X : ℝ} (hX : 0 ≤ X)
    (hx : |(x : ℝ)| ≤ X) (hy : |(y : ℝ)| ≤ X) :
    |rationalQuadraticAlgebraRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| ≤
      formIdealVectorRealHeightMajorant D Q X := by
  rw [rationalQuadraticAlgebraRealEmbedding_formIdealVector]
  unfold formIdealVectorRealHeightMajorant
  have h := abs_realEmbedding_formIdealVector_le_majorant_aux
    (a := (Q.a : ℝ)) (b := (Q.b : ℝ))
    (s := -Real.sqrt (D : ℝ)) (x := (x : ℝ)) (y := (y : ℝ))
    (X := X) hX hx hy
  simpa only [sub_eq_add_neg, abs_neg,
    abs_of_nonneg (Real.sqrt_nonneg _)] using h

/-- Absolute-value upper bound at the conjugate displayed embedding. -/
theorem abs_rationalQuadraticAlgebraNegativeRealEmbedding_formIdealVector_le_majorant
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    {x y : ℤ} {X : ℝ} (hX : 0 ≤ X)
    (hx : |(x : ℝ)| ≤ X) (hy : |(y : ℝ)| ≤ X) :
    |rationalQuadraticAlgebraNegativeRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| ≤
      formIdealVectorRealHeightMajorant D Q X := by
  rw [rationalQuadraticAlgebraNegativeRealEmbedding_formIdealVector]
  unfold formIdealVectorRealHeightMajorant
  simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using
    (abs_realEmbedding_formIdealVector_le_majorant_aux
      (a := (Q.a : ℝ)) (b := (Q.b : ℝ))
      (s := Real.sqrt (D : ℝ)) (x := (x : ℝ)) (y := (y : ℝ))
      (X := X) hX hx hy)

/-- The product of the two displayed real values is the signed norm
`a * Q(x,y)`. -/
theorem realEmbeddings_formIdealVector_mul_eq
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (x y : ℤ) :
    rationalQuadraticAlgebraRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D) *
      rationalQuadraticAlgebraNegativeRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D) =
      (Q.a : ℝ) * (Q.eval x y : ℝ) := by
  rw [rationalQuadraticAlgebraRealEmbedding_formIdealVector,
    rationalQuadraticAlgebraNegativeRealEmbedding_formIdealVector]
  have hsqrt : (Real.sqrt (D : ℝ)) ^ 2 = (D : ℝ) := by
    exact Real.sq_sqrt (by exact_mod_cast hD)
  have hdisc : (Q.b : ℝ) ^ 2 - 4 * (Q.a : ℝ) * (Q.c : ℝ) = (D : ℝ) := by
    exact_mod_cast hQ
  simp only [eval, Int.cast_add, Int.cast_mul, Int.cast_pow]
  nlinarith

/-- A nonzero represented value supplies a positive reciprocal lower bound
at the positive real embedding, while the coordinate box supplies the common
upper bound.  This is the `[L,H]` window required by the one-ideal-fibre unit
orbit count. -/
theorem abs_rationalQuadraticAlgebraRealEmbedding_formIdealVector_mem_reciprocal_heightWindow
    (D : ℤ) (hD : 0 ≤ D) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (ha : Q.a ≠ 0) (m : ℤ) (hm : m ≠ 0)
    {x y : ℤ} (hvalue : Q.eval x y = m)
    {X : ℝ} (hX : 0 ≤ X)
    (hx : |(x : ℝ)| ≤ X) (hy : |(y : ℝ)| ≤ X) :
    let H := formIdealVectorRealHeightMajorant D Q X
    let L := |(Q.a : ℝ) * (m : ℝ)| / H
    0 < L ∧
      L ≤ |rationalQuadraticAlgebraRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| ∧
      |rationalQuadraticAlgebraRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| ≤ H := by
  dsimp only
  let H := formIdealVectorRealHeightMajorant D Q X
  have hH : 0 < H := formIdealVectorRealHeightMajorant_pos D hD Q hX
  have hposUpper :
      |rationalQuadraticAlgebraRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| ≤ H :=
    abs_rationalQuadraticAlgebraRealEmbedding_formIdealVector_le_majorant
      D hD Q hQ hX hx hy
  have hnegUpper :
      |rationalQuadraticAlgebraNegativeRealEmbedding D hD
        (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| ≤ H :=
    abs_rationalQuadraticAlgebraNegativeRealEmbedding_formIdealVector_le_majorant
      D hD Q hQ hX hx hy
  have hprod :
      |rationalQuadraticAlgebraRealEmbedding D hD
          (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| *
        |rationalQuadraticAlgebraNegativeRealEmbedding D hD
          (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| =
        |(Q.a : ℝ) * (m : ℝ)| := by
    rw [← abs_mul, realEmbeddings_formIdealVector_mul_eq, hvalue]
  have hnumPos : 0 < |(Q.a : ℝ) * (m : ℝ)| := by
    apply abs_pos.mpr
    exact mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hm)
  refine ⟨div_pos hnumPos hH, ?_, hposUpper⟩
  apply (div_le_iff₀ hH).mpr
  calc
    |(Q.a : ℝ) * (m : ℝ)| =
        |rationalQuadraticAlgebraRealEmbedding D hD
          (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| *
        |rationalQuadraticAlgebraNegativeRealEmbedding D hD
          (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| := hprod.symm
    _ ≤ |rationalQuadraticAlgebraRealEmbedding D hD
          (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D)| * H :=
      mul_le_mul_of_nonneg_left hnegUpper (abs_nonneg _)

end
end IntegralBinaryQuadraticForm
end PellPaper
