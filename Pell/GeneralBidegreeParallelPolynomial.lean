import Pell.GeneralBidegreeGridAlgebra
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The parallel-line polynomial as a genuine evaluation-kernel element

The rank-cap step in `L:sheared` of `main.tex` uses the polynomial

`P(N₁,N₂) = ∏_{a=0}^A (N₁ - 2N₂ - a)`.

This module realizes that expression as an `MvPolynomial` over `ℚ`, proves
that it is nonzero, and proves that it and all of its polynomial multiples
vanish on the literal finite sheared grid `Γ_{A,B}`.  Thus the polynomial
ideal used in the manuscript is an actual subspace of the finite-grid
evaluation kernel.  Weighted support and dimension estimates remain separate.
-/

namespace PellPaper

open scoped BigOperators

/-- Evaluation of a two-variable polynomial at `(N₁,N₂)`.  The variables are
the two elements of `Fin 2`, in that order. -/
def shearedPolynomialEvalAt (N₁ N₂ : ℚ) :
    MvPolynomial (Fin 2) ℚ →+* ℚ :=
  MvPolynomial.eval (Fin.cases N₁ (fun _ => N₂))

@[simp]
theorem shearedPolynomialEvalAt_X_zero (N₁ N₂ : ℚ) :
    shearedPolynomialEvalAt N₁ N₂ (MvPolynomial.X (0 : Fin 2)) = N₁ := by
  simp [shearedPolynomialEvalAt]

@[simp]
theorem shearedPolynomialEvalAt_X_one (N₁ N₂ : ℚ) :
    shearedPolynomialEvalAt N₁ N₂ (MvPolynomial.X (1 : Fin 2)) = N₂ := by
  simp only [shearedPolynomialEvalAt, MvPolynomial.eval_X]
  have hindex : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
  rw [hindex, Fin.cases_succ]

/-- The parallel-line annihilator for the grid `Γ_{A,B}`, now represented as
a rational bivariate polynomial. -/
noncomputable def generalBidegreeParallelLinePolynomial (A : ℕ) :
    MvPolynomial (Fin 2) ℚ :=
  ∏ a ∈ Finset.range (A + 1),
    (MvPolynomial.X (0 : Fin 2) - 2 * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (a : ℚ))

/-- Explicit evaluation formula for the parallel-line polynomial. -/
theorem shearedPolynomialEvalAt_generalBidegreeParallelLinePolynomial
    (A : ℕ) (N₁ N₂ : ℚ) :
    shearedPolynomialEvalAt N₁ N₂ (generalBidegreeParallelLinePolynomial A) =
      ∏ a ∈ Finset.range (A + 1), (N₁ - 2 * N₂ - (a : ℚ)) := by
  rw [generalBidegreeParallelLinePolynomial, map_prod]
  apply Finset.prod_congr rfl
  intro a _
  have htwo : shearedPolynomialEvalAt N₁ N₂
      (2 : MvPolynomial (Fin 2) ℚ) = 2 := by
    simp [shearedPolynomialEvalAt]
  have hC : shearedPolynomialEvalAt N₁ N₂
      (MvPolynomial.C (a : ℚ)) = (a : ℚ) := by
    simp [shearedPolynomialEvalAt]
  rw [map_sub, map_sub, map_mul, htwo,
    shearedPolynomialEvalAt_X_zero, shearedPolynomialEvalAt_X_one, hC]

/-- The parallel-line polynomial vanishes at every indexed point of the
literal sheared grid. -/
theorem shearedPolynomialEvalAt_generalBidegreeParallelLinePolynomial_gridPoint
    (A B : ℕ) (a : Fin (A + 1)) (b : Fin (B + 1)) :
    shearedPolynomialEvalAt
      ((a.1 + 2 * b.1 : ℕ) : ℚ) (b.1 : ℚ)
      (generalBidegreeParallelLinePolynomial A) = 0 := by
  rw [shearedPolynomialEvalAt_generalBidegreeParallelLinePolynomial]
  apply Finset.prod_eq_zero (i := a.1)
  · exact Finset.mem_range.mpr a.2
  · push_cast
    ring

/-- The parallel-line polynomial is nonzero.  Evaluation just beyond the
last parallel line gives a product of nonzero positive factors. -/
theorem generalBidegreeParallelLinePolynomial_ne_zero (A : ℕ) :
    generalBidegreeParallelLinePolynomial A ≠ 0 := by
  intro hzero
  have heval := congrArg
    (shearedPolynomialEvalAt ((A + 1 : ℕ) : ℚ) 0) hzero
  rw [shearedPolynomialEvalAt_generalBidegreeParallelLinePolynomial] at heval
  have hprod :
      (Finset.range (A + 1)).prod
        (fun a => ((A + 1 : ℕ) : ℚ) - (a : ℚ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro a ha
    have hlt : a < A + 1 := Finset.mem_range.mp ha
    have hpos : 0 < ((A + 1 : ℕ) : ℚ) - (a : ℚ) := by
      apply sub_pos.mpr
      exact_mod_cast hlt
    exact ne_of_gt hpos
  apply hprod
  simpa using heval

/-- The finite-grid evaluation map for arbitrary rational bivariate
polynomials. -/
noncomputable def generalBidegreeGridPolynomialEvaluationLinearMap (A B : ℕ) :
    MvPolynomial (Fin 2) ℚ →ₗ[ℚ] (generalBidegreeGrid A B → ℚ) where
  toFun P := fun p => shearedPolynomialEvalAt (p.1.1 : ℚ) (p.1.2 : ℚ) P
  map_add' P Q := by
    ext p
    simp [shearedPolynomialEvalAt]
  map_smul' c P := by
    ext p
    simp [shearedPolynomialEvalAt, smul_eq_mul]

/-- The evaluation map sends the parallel-line polynomial to zero on the
entire sheared grid. -/
theorem generalBidegreeParallelLinePolynomial_mem_gridEvaluation_ker
    (A B : ℕ) :
    generalBidegreeParallelLinePolynomial A ∈
      (generalBidegreeGridPolynomialEvaluationLinearMap A B).ker := by
  rw [LinearMap.mem_ker]
  ext p
  rcases generalBidegreeGridPoint_surjective A B p with ⟨⟨a, b⟩, rfl⟩
  simpa [generalBidegreeGridPolynomialEvaluationLinearMap,
    generalBidegreeGridPoint] using
    shearedPolynomialEvalAt_generalBidegreeParallelLinePolynomial_gridPoint A B a b

/-- Every polynomial multiple of the parallel-line polynomial is also in
the finite-grid evaluation kernel. -/
theorem mul_generalBidegreeParallelLinePolynomial_mem_gridEvaluation_ker
    (A B : ℕ) (Q : MvPolynomial (Fin 2) ℚ) :
    generalBidegreeParallelLinePolynomial A * Q ∈
      (generalBidegreeGridPolynomialEvaluationLinearMap A B).ker := by
  rw [LinearMap.mem_ker]
  ext p
  have hP : shearedPolynomialEvalAt (p.1.1 : ℚ) (p.1.2 : ℚ)
      (generalBidegreeParallelLinePolynomial A) = 0 := by
    rcases generalBidegreeGridPoint_surjective A B p with ⟨⟨a, b⟩, hp⟩
    subst p
    simpa [generalBidegreeGridPoint] using
      shearedPolynomialEvalAt_generalBidegreeParallelLinePolynomial_gridPoint A B a b
  change shearedPolynomialEvalAt (p.1.1 : ℚ) (p.1.2 : ℚ)
    (generalBidegreeParallelLinePolynomial A * Q) = 0
  rw [map_mul, hP, zero_mul]

end PellPaper
