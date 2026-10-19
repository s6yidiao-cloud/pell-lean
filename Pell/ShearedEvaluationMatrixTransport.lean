import Pell.GeneralBidegreeAuxiliaryRelation
import Pell.TwoLayerShearedExponentialIdentity

/-!
# Exact transport from affine monomials to sheared exponential columns

In the determinant proof of `L:sheared` in `main.tex`, a local centre `s₀`
is extracted from the affine columns `s^a t^b`.  Writing
`s = s₀ S` and `t = s₀² T` produces a column factor
`s₀^(a + 2b)` and leaves the sheared exponential column

`exp ((a + 2b) log S + b log (T / S²))`.

This file proves that identity simultaneously for a finite evaluation
matrix, including the exact determinant factor for every selected square
minor.  It does not estimate the resulting exponential determinant.
-/

namespace PellPaper

open scoped BigOperators

/-- Scale column `j` of a matrix by `d j`. -/
def columnScale {ι κ R : Type*} [Mul R] (d : κ → R)
    (A : Matrix ι κ R) : Matrix ι κ R :=
  fun i j => A i j * d j

/-- The affine monomial column indexed by the exponent pair `(a,b)`. -/
def affineMonomialEntry (s t : ℝ) (ab : generalBidegreeFormIndex A B) : ℝ :=
  s ^ ab.1.1 * t ^ ab.2.1

/-- The local column factor extracted from the centre `s₀`. -/
def shearedCenterColumnScale (s₀ : ℝ) (ab : generalBidegreeFormIndex A B) : ℝ :=
  s₀ ^ (ab.1.1 + 2 * ab.2.1)

/-- The remaining exponential column in sheared logarithmic coordinates. -/
noncomputable def shearedExponentialEntry (S T : ℝ)
    (ab : generalBidegreeFormIndex A B) : ℝ :=
  Real.exp (((ab.1.1 + 2 * ab.2.1 : ℕ) : ℝ) * Real.log S +
    (ab.2.1 : ℝ) * (Real.log T - 2 * Real.log S))

/-- The affine evaluation matrix after expressing each row as
`(s,t) = (s₀ S, s₀² T)`. -/
def centeredAffineEvaluationMatrix {ι : Type*} (A B : ℕ)
    (s₀ : ℝ) (S T : ι → ℝ) :
    Matrix ι (generalBidegreeFormIndex A B) ℝ :=
  fun r ab => affineMonomialEntry (s₀ * S r) (s₀ ^ 2 * T r) ab

/-- The sheared exponential evaluation matrix left after extracting the
centre from every affine column. -/
noncomputable def shearedExponentialEvaluationMatrix {ι : Type*} (A B : ℕ)
    (S T : ι → ℝ) :
    Matrix ι (generalBidegreeFormIndex A B) ℝ :=
  fun r ab => shearedExponentialEntry (S r) (T r) ab

/-- One local affine monomial is exactly its centre factor times the
corresponding sheared exponential column. -/
theorem affineMonomialEntry_centered_eq_shearedCenter_mul_exponential
    {s₀ S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (a b : ℕ) :
    (s₀ * S) ^ a * (s₀ ^ 2 * T) ^ b =
      s₀ ^ (a + 2 * b) *
        Real.exp (((a + 2 * b : ℕ) : ℝ) * Real.log S +
          (b : ℝ) * (Real.log T - 2 * Real.log S)) := by
  calc
    (s₀ * S) ^ a * (s₀ ^ 2 * T) ^ b =
        (s₀ ^ a * s₀ ^ (2 * b)) * (S ^ a * T ^ b) := by
          rw [mul_pow, mul_pow, ← pow_mul]
          ring
    _ = s₀ ^ (a + 2 * b) * (S ^ a * T ^ b) := by
      rw [← pow_add]
    _ = _ := by rw [twoLayer_pow_mul_eq_exp_shearedLog hS hT a b]

/-- Entrywise, local affine evaluation is the column-scaled sheared
exponential evaluation matrix. -/
theorem centeredAffineEvaluationMatrix_eq_columnScale_shearedExponential
    {ι : Type*} (A B : ℕ) (s₀ : ℝ) (S T : ι → ℝ)
    (hS : ∀ r, 0 < S r) (hT : ∀ r, 0 < T r) :
    centeredAffineEvaluationMatrix A B s₀ S T =
      columnScale (shearedCenterColumnScale (A := A) (B := B) s₀)
        (shearedExponentialEvaluationMatrix A B S T) := by
  ext r ab
  rcases ab with ⟨a, b⟩
  simp only [centeredAffineEvaluationMatrix, affineMonomialEntry,
    columnScale, shearedExponentialEvaluationMatrix, shearedExponentialEntry,
    shearedCenterColumnScale]
  rw [affineMonomialEntry_centered_eq_shearedCenter_mul_exponential
    (hS r) (hT r) a.1 b.1]
  ring

/-- The total exponent of the extracted centre over the full bidegree grid. -/
def shearedCenterExponent (A B : ℕ) : ℕ :=
  Finset.univ.sum (fun ab : generalBidegreeFormIndex A B =>
    ab.1.1 + 2 * ab.2.1)

/-- The product of all column-centre factors has the expected summed
exponent. -/
theorem prod_shearedCenterColumnScale (A B : ℕ) (s₀ : ℝ) :
    ∏ ab : generalBidegreeFormIndex A B,
      shearedCenterColumnScale (A := A) (B := B) s₀ ab =
        s₀ ^ shearedCenterExponent A B := by
  unfold shearedCenterColumnScale shearedCenterExponent
  exact Finset.prod_pow_eq_pow_sum Finset.univ
    (fun ab : generalBidegreeFormIndex A B => ab.1.1 + 2 * ab.2.1) s₀

/-- Every selected full affine minor is the corresponding sheared
exponential minor times the explicit product of centre-column factors. -/
theorem det_centeredAffineEvaluationMatrix_submatrix_eq_centerFactor_mul
    {ι : Type*} (A B : ℕ) (s₀ : ℝ) (S T : ι → ℝ)
    (hS : ∀ r, 0 < S r) (hT : ∀ r, 0 < T r)
    (r : generalBidegreeFormIndex A B ↪ ι) :
    ((centeredAffineEvaluationMatrix A B s₀ S T).submatrix r id).det =
      (∏ ab : generalBidegreeFormIndex A B,
        shearedCenterColumnScale (A := A) (B := B) s₀ ab) *
        ((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det := by
  classical
  rw [centeredAffineEvaluationMatrix_eq_columnScale_shearedExponential
    A B s₀ S T hS hT]
  let d := shearedCenterColumnScale (A := A) (B := B) s₀
  let E := shearedExponentialEvaluationMatrix A B S T
  have hmatrix : (columnScale d E).submatrix r id =
      Matrix.of fun i j => d j * (E.submatrix r id) i j := by
    ext i j
    simp [columnScale, d, E, mul_comm]
  rw [hmatrix]
  exact Matrix.det_mul_row d (E.submatrix r id)

end PellPaper
