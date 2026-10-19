import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Rectangular determinant expansion through injective column choices

This file develops the arbitrary finite-dimensional Leibniz expansion that
precedes Cauchy--Binet: for `U : n × m` and `V : m × n`, the determinant of
`U * V` is a sum over injective maps `n → m`.  Each term is a selected minor
of `U` times the matching diagonal product from `V`.

The further regrouping of these injection terms into one product of two
minors per *unordered* support is the remaining full Cauchy--Binet step.
-/

namespace PellPaper

open scoped BigOperators

/-- Before discarding repeated column choices, the rectangular determinant
expansion is a sum over all functions from the square index set into the
intermediate index set. -/
theorem det_mul_rectangular_eq_sum_all_functions
    {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [CommRing R]
    (U : Matrix n m R) (V : Matrix m n R) :
    (U * V).det =
      ∑ p : n → m, (U.submatrix id p).det * ∏ i, V (p i) i := by
  classical
  calc
    (U * V).det =
        ∑ p : n → m, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ∏ i, U (σ i) (p i) * V (p i) i := by
          simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
            Finset.mul_sum, Fintype.piFinset_univ]
          rw [Finset.sum_comm]
    _ = ∑ p : n → m, (U.submatrix id p).det * ∏ i, V (p i) i := by
          simp_rw [Matrix.det_apply']
          simp only [Matrix.submatrix_apply]
          simp_rw [Finset.prod_mul_distrib]
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro σ _
          simp only [id_eq]
          ring

/-- A repeated column choice gives a zero selected determinant. -/
theorem det_submatrix_eq_zero_of_not_injective
    {n m R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (U : Matrix n m R) (p : n → m) (hp : ¬ Function.Injective p) :
    (U.submatrix id p).det = 0 := by
  obtain ⟨i, j, hij, hpij⟩ : ∃ i j : n, i ≠ j ∧ p i = p j := by
    by_contra hcollision
    apply hp
    intro i j hpij
    by_contra hij
    exact hcollision ⟨i, j, hij, hpij⟩
  apply Matrix.det_zero_of_column_eq hij
  intro k
  simp [Matrix.submatrix_apply, hpij]

/-- The all-functions expansion reduces exactly to injective column choices.
This is an arbitrary finite-dimensional rectangular determinant identity;
the terms are indexed by ordered supports. -/
theorem det_mul_rectangular_eq_sum_injective
    {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [CommRing R]
    (U : Matrix n m R) (V : Matrix m n R) :
    (U * V).det =
      ∑ p : {p : n → m // Function.Injective p},
        (U.submatrix id p.1).det * ∏ i, V (p.1 i) i := by
  classical
  rw [det_mul_rectangular_eq_sum_all_functions]
  let f : (n → m) → R := fun p =>
    (U.submatrix id p).det * ∏ i, V (p i) i
  change (∑ p : n → m, f p) =
    ∑ p : {p : n → m // Function.Injective p}, f p.1
  calc
    (∑ p : n → m, f p) =
        (∑ p : {p : n → m // Function.Injective p}, f p.1) +
          ∑ p : {p : n → m // ¬ Function.Injective p}, f p.1 := by
            simpa only using
              (Fintype.sum_subtype_add_sum_subtype
                (fun p : n → m => Function.Injective p) f).symm
    _ = ∑ p : {p : n → m // Function.Injective p}, f p.1 := by
          have hzero : (∑ p : {p : n → m // ¬ Function.Injective p},
              f p.1) = 0 := by
            apply Finset.sum_eq_zero
            intro p _
            dsimp [f]
            rw [det_submatrix_eq_zero_of_not_injective U p.1 p.2, zero_mul]
          rw [hzero, add_zero]

/-- A nonzero determinant of a rectangular product has a nonzero term in the
arbitrary finite injection expansion.  Thus some injective column choice has
both a nonzero selected `U` minor and a nonzero matching diagonal coefficient
product from `V`. -/
theorem exists_injective_rectangular_term_of_det_mul_ne_zero
    {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [CommRing R]
    (U : Matrix n m R) (V : Matrix m n R)
    (hdet : (U * V).det ≠ 0) :
    ∃ p : {p : n → m // Function.Injective p},
      (U.submatrix id p.1).det ≠ 0 ∧ ∏ i, V (p.1 i) i ≠ 0 := by
  classical
  have hsum :
      (∑ p : {p : n → m // Function.Injective p},
        (U.submatrix id p.1).det * ∏ i, V (p.1 i) i) ≠ 0 := by
    intro hzero
    apply hdet
    rw [det_mul_rectangular_eq_sum_injective]
    exact hzero
  by_contra hnone
  apply hsum
  apply Finset.sum_eq_zero
  intro p _
  by_cases hU : (U.submatrix id p.1).det = 0
  · rw [hU, zero_mul]
  by_cases hV : (∏ i, V (p.1 i) i) = 0
  · rw [hV, mul_zero]
  exact False.elim (hnone ⟨p, hU, hV⟩)

end PellPaper
