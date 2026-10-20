import Pell.SourceNormalizedShearedRankCaps

/-!
# Explicit sums of source-normalized lattice-boundary errors

The two source-normalized rank caps retain an explicit boundary loss at each
mesh point.  This file bounds their finite low and high mesh sums at the
source mesh `x / B` by elementary polynomials.  No limiting argument or
asymptotic notation is used.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The mesh-scaled sum of triangular-cap boundary errors over the first `A`
source mesh cells. -/
def sourceNormalizedLowMeshBoundaryErrorSum (A B : ℕ) (m x : ℝ) : ℝ :=
  (x / (B : ℝ)) *
    ∑ n ∈ Finset.range A,
      sourceNormalizedTriangularCapError B m x
        (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))

/-- The mesh-scaled sum of shifted-shell boundary errors over `Nhigh` cells
after the source crossover `x * (A / B)`. -/
def sourceNormalizedHighMeshBoundaryErrorSum
    (A B Nhigh : ℕ) (m x : ℝ) : ℝ :=
  (x / (B : ℝ)) *
    ∑ n ∈ Finset.range Nhigh,
      sourceNormalizedShellCapError B m x
        (x * ((A : ℝ) / (B : ℝ)) +
          ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))

/-- At a low source mesh point the triangular boundary error has a simple
linear form in the mesh index. -/
theorem sourceNormalizedTriangularCapError_at_lowMesh
    (B n : ℕ) (m x : ℝ) (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) :
    sourceNormalizedTriangularCapError B m x
      (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) =
      ((n + 1 : ℕ) : ℝ) * (x / m + 1) + 1 := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  rw [sourceNormalizedTriangularCapError]
  field_simp [ne_of_gt hB_real, ne_of_gt hm, ne_of_gt hx]

/-- At a translated high source mesh point the shell boundary error is a
linear form in the total mesh index `A + n + 1`. -/
theorem sourceNormalizedShellCapError_at_highMesh
    (A B n : ℕ) (m x : ℝ) (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) :
    sourceNormalizedShellCapError B m x
      (x * ((A : ℝ) / (B : ℝ)) +
        ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) =
      ((A : ℝ) + ((n + 1 : ℕ) : ℝ)) * (3 * x / (2 * m) + 1) + 1 := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  rw [sourceNormalizedShellCapError]
  field_simp [ne_of_gt hB_real, ne_of_gt hm, ne_of_gt hx]

/-- A finite polynomial upper bound for the low-branch boundary-error sum.
The bound is deliberately endpoint-based: it avoids any rounding or limit
arguments while retaining the useful `x / B` mesh factor. -/
theorem sourceNormalizedLowMeshBoundaryErrorSum_le_polynomial
    (A B : ℕ) (m x : ℝ) (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) :
    sourceNormalizedLowMeshBoundaryErrorSum A B m x ≤
      (x / (B : ℝ)) * (A : ℝ) *
        ((A : ℝ) * (x / m + 1) + 1) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hmesh_nonneg : 0 ≤ x / (B : ℝ) := by positivity
  have hpoint : ∀ n ∈ Finset.range A,
      sourceNormalizedTriangularCapError B m x
        (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) ≤
        (A : ℝ) * (x / m + 1) + 1 := by
    intro n hn
    rw [sourceNormalizedTriangularCapError_at_lowMesh B n m x hB hm hx]
    have hnlt : n < A := Finset.mem_range.mp hn
    have hnle : n + 1 ≤ A := by omega
    have hcoef : 0 ≤ x / m + 1 := by positivity
    have hcast : ((n + 1 : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hnle
    nlinarith [mul_le_mul_of_nonneg_right hcast hcoef]
  unfold sourceNormalizedLowMeshBoundaryErrorSum
  calc
    (x / (B : ℝ)) *
        ∑ n ∈ Finset.range A,
          sourceNormalizedTriangularCapError B m x
            (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) ≤
        (x / (B : ℝ)) *
          ∑ _n ∈ Finset.range A, ((A : ℝ) * (x / m + 1) + 1) := by
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) hmesh_nonneg
    _ = (x / (B : ℝ)) * (A : ℝ) *
          ((A : ℝ) * (x / m + 1) + 1) := by
            rw [Finset.sum_const]
            simp only [Finset.card_range]
            ring

/-- A finite polynomial upper bound for the high-branch boundary-error sum.
It keeps the exact finite high-cell count `Nhigh` and the source mesh factor
`x / B`. -/
theorem sourceNormalizedHighMeshBoundaryErrorSum_le_polynomial
    (A B Nhigh : ℕ) (m x : ℝ) (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) :
    sourceNormalizedHighMeshBoundaryErrorSum A B Nhigh m x ≤
      (x / (B : ℝ)) * (Nhigh : ℝ) *
        (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hmesh_nonneg : 0 ≤ x / (B : ℝ) := by positivity
  have hpoint : ∀ n ∈ Finset.range Nhigh,
      sourceNormalizedShellCapError B m x
        (x * ((A : ℝ) / (B : ℝ)) +
          ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) ≤
        ((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1 := by
    intro n hn
    rw [sourceNormalizedShellCapError_at_highMesh A B n m x hB hm hx]
    have hnlt : n < Nhigh := Finset.mem_range.mp hn
    have hnle : n + 1 ≤ Nhigh := by omega
    have hcoef : 0 ≤ 3 * x / (2 * m) + 1 := by positivity
    have hcast : ((n + 1 : ℕ) : ℝ) ≤ (Nhigh : ℝ) := by exact_mod_cast hnle
    nlinarith [mul_le_mul_of_nonneg_right
      (add_le_add_left hcast (A : ℝ)) hcoef]
  unfold sourceNormalizedHighMeshBoundaryErrorSum
  calc
    (x / (B : ℝ)) *
        ∑ n ∈ Finset.range Nhigh,
          sourceNormalizedShellCapError B m x
            (x * ((A : ℝ) / (B : ℝ)) +
              ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) ≤
        (x / (B : ℝ)) *
          ∑ _n ∈ Finset.range Nhigh,
            (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1) := by
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) hmesh_nonneg
    _ = (x / (B : ℝ)) * (Nhigh : ℝ) *
          (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1) := by
            rw [Finset.sum_const]
            simp only [Finset.card_range]
            ring

/-- The two explicit branch bounds combine into one finite error budget. -/
theorem sourceNormalizedMeshBoundaryErrorSums_le_polynomial
    (A B Nhigh : ℕ) (m x : ℝ) (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) :
    sourceNormalizedLowMeshBoundaryErrorSum A B m x +
      sourceNormalizedHighMeshBoundaryErrorSum A B Nhigh m x ≤
      (x / (B : ℝ)) *
        ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
          (Nhigh : ℝ) *
            (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1)) := by
  have hlow := sourceNormalizedLowMeshBoundaryErrorSum_le_polynomial
    A B m x hB hm hx
  have hhigh := sourceNormalizedHighMeshBoundaryErrorSum_le_polynomial
    A B Nhigh m x hB hm hx
  calc
    sourceNormalizedLowMeshBoundaryErrorSum A B m x +
        sourceNormalizedHighMeshBoundaryErrorSum A B Nhigh m x ≤
        (x / (B : ℝ)) * (A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
          (x / (B : ℝ)) * (Nhigh : ℝ) *
            (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1) :=
      add_le_add hlow hhigh
    _ = (x / (B : ℝ)) *
        ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
          (Nhigh : ℝ) *
            (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1)) := by
      ring

/-- The error expression occurring in the source-normalized actual-rank
cubic bound is exactly the sum of the two named branch budgets. -/
theorem sourceNormalized_mesh_errorSum_eq_low_add_high
    (A B Nhigh : ℕ) (m x : ℝ) :
    (x / (B : ℝ)) *
      ((∑ n ∈ Finset.range A,
          sourceNormalizedTriangularCapError B m x
            (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
        ∑ n ∈ Finset.range Nhigh,
          sourceNormalizedShellCapError B m x
            (x * ((A : ℝ) / (B : ℝ)) +
              ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) =
      sourceNormalizedLowMeshBoundaryErrorSum A B m x +
        sourceNormalizedHighMeshBoundaryErrorSum A B Nhigh m x := by
  unfold sourceNormalizedLowMeshBoundaryErrorSum
    sourceNormalizedHighMeshBoundaryErrorSum
  ring

/-- Direct polynomial bound for the precise low-plus-high error expression
which appears in `sourceNormalized_actualRankDeficits_ge_cubic_sub_errors`. -/
theorem sourceNormalized_mesh_errorSum_le_polynomial
    (A B Nhigh : ℕ) (m x : ℝ) (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) :
    (x / (B : ℝ)) *
      ((∑ n ∈ Finset.range A,
          sourceNormalizedTriangularCapError B m x
            (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
        ∑ n ∈ Finset.range Nhigh,
          sourceNormalizedShellCapError B m x
            (x * ((A : ℝ) / (B : ℝ)) +
              ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) ≤
      (x / (B : ℝ)) *
        ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
          (Nhigh : ℝ) *
            (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1)) := by
  rw [sourceNormalized_mesh_errorSum_eq_low_add_high]
  exact sourceNormalizedMeshBoundaryErrorSums_le_polynomial
    A B Nhigh m x hB hm hx

end

end PellPaper
