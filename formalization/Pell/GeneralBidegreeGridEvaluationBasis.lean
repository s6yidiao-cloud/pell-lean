import Pell.GeneralBidegreeGridAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The sheared monomial basis on the finite general-bidegree grid

This module records the unrestricted finite-dimensional separation fact for
the grid `Γ_{A,B}`.  The functions

`(N₁, N₂) ↦ (N₁ - 2N₂)^a N₂^b`,

for `0 ≤ a ≤ A` and `0 ≤ b ≤ B`, form a rational basis of all functions on
the grid.  Equivalently, their evaluation map is a linear equivalence.

This is only the exact finite-grid rank statement preceding the weighted
rank-filtration and determinant arguments in `L:sheared` of `main.tex`.  It
does not estimate a weighted rank, a determinant, a coefficient height, or a
solution count.
-/

namespace PellPaper

open scoped BigOperators

/-- The sheared-coordinate monomial `(N₁ - 2N₂)^a N₂^b`. -/
def generalBidegreeShearedMonomial
    (ab : generalBidegreeGridIndex A B) (N₁ N₂ : ℚ) : ℚ :=
  (N₁ - 2 * N₂) ^ ab.1.1 * N₂ ^ ab.2.1

/-- The restriction of a sheared-coordinate monomial to `Γ_{A,B}`. -/
def generalBidegreeGridBasisFunction (A B : ℕ)
    (ab : generalBidegreeGridIndex A B) :
    generalBidegreeGrid A B → ℚ :=
  fun p => generalBidegreeShearedMonomial ab (p.1.1 : ℚ) (p.1.2 : ℚ)

/-- Evaluation of a coefficient vector against the sheared-coordinate
monomial family on `Γ_{A,B}`. -/
noncomputable def generalBidegreeGridBasisEvaluation (A B : ℕ) :
    (generalBidegreeGridIndex A B → ℚ) →ₗ[ℚ]
      (generalBidegreeGrid A B → ℚ) where
  toFun c := fun p => ∑ ab, c ab * generalBidegreeGridBasisFunction A B ab p
  map_add' c d := by
    ext p
    simp only [Pi.add_apply]
    simp_rw [add_mul]
    exact Finset.sum_add_distrib
  map_smul' q c := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]

/-- At the grid point indexed by `(a,b)`, the sheared monomial has the
expected ordinary product value `a^i b^j`. -/
theorem generalBidegreeGridBasisFunction_eval_gridPoint
    (A B : ℕ) (ab : generalBidegreeGridIndex A B)
    (a : Fin (A + 1)) (b : Fin (B + 1)) :
    generalBidegreeGridBasisFunction A B ab
      (generalBidegreeGridPoint A B (a, b)) =
        (a.1 : ℚ) ^ ab.1.1 * (b.1 : ℚ) ^ ab.2.1 := by
  unfold generalBidegreeGridBasisFunction generalBidegreeShearedMonomial
  simp only [generalBidegreeGridPoint]
  push_cast
  congr 1
  ring

/-- The coefficient evaluation formula at an indexed point of the grid. -/
theorem generalBidegreeGridBasisEvaluation_apply_gridPoint
    (A B : ℕ) (c : generalBidegreeGridIndex A B → ℚ)
    (a : Fin (A + 1)) (b : Fin (B + 1)) :
    generalBidegreeGridBasisEvaluation A B c
      (generalBidegreeGridPoint A B (a, b)) =
        ∑ ab, c ab * (a.1 : ℚ) ^ ab.1.1 * (b.1 : ℚ) ^ ab.2.1 := by
  unfold generalBidegreeGridBasisEvaluation
  change (∑ ab, c ab * generalBidegreeGridBasisFunction A B ab
    (generalBidegreeGridPoint A B (a, b))) = _
  apply Finset.sum_congr rfl
  intro ab _
  rw [generalBidegreeGridBasisFunction_eval_gridPoint]
  ring

/-! The next two lemmas are the tensor-product Vandermonde argument. -/

/-- If a coefficient vector evaluates to zero on the grid, then it is zero. -/
theorem generalBidegreeGridBasisEvaluation_eq_zero_iff
    (A B : ℕ) (c : generalBidegreeGridIndex A B → ℚ) :
    generalBidegreeGridBasisEvaluation A B c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hgrid : ∀ (a : Fin (A + 1)) (b : Fin (B + 1)),
        ∑ ab, c ab * (a.1 : ℚ) ^ ab.1.1 * (b.1 : ℚ) ^ ab.2.1 = 0 := by
      intro a b
      have hpoint := congr_fun h (generalBidegreeGridPoint A B (a, b))
      rw [generalBidegreeGridBasisEvaluation_apply_gridPoint] at hpoint
      simpa using hpoint
    have hfirst : ∀ b : Fin (B + 1),
        (fun i : Fin (A + 1) =>
          ∑ j : Fin (B + 1), c (i, j) * (b.1 : ℚ) ^ j.1) = 0 := by
      intro b
      apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
        (finiteLagrangeNode_injective (A + 1))
      intro a
      rw [← hgrid a b]
      rw [Fintype.sum_prod_type]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    funext ij
    rcases ij with ⟨i, j⟩
    have hsecond : (fun k : Fin (B + 1) => c (i, k)) = 0 := by
      apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
        (finiteLagrangeNode_injective (B + 1))
      intro b
      have hvalue := congr_fun (hfirst b) i
      simpa using hvalue
    exact congr_fun hsecond j
  · intro h
    rw [h]
    exact map_zero _

/-- The sheared monomial evaluation map is injective. -/
theorem generalBidegreeGridBasisEvaluation_injective (A B : ℕ) :
    Function.Injective (generalBidegreeGridBasisEvaluation A B) := by
  intro c d h
  have hzero : generalBidegreeGridBasisEvaluation A B (c - d) = 0 := by
    rw [map_sub, h]
    exact sub_self _
  have hcd : c - d = 0 :=
    (generalBidegreeGridBasisEvaluation_eq_zero_iff A B (c - d)).mp hzero
  exact sub_eq_zero.mp hcd

/-- The canonical equivalence from bounded coefficient indices to grid
points. -/
noncomputable def generalBidegreeGridPointEquiv (A B : ℕ) :
    generalBidegreeGridIndex A B ≃ generalBidegreeGrid A B :=
  Equiv.ofBijective _ (generalBidegreeGridPoint_bijective A B)

/-- The source and target function spaces of the evaluation map have equal
finite dimension. -/
theorem finrank_generalBidegreeGridBasisEvaluation_source_eq_target (A B : ℕ) :
    Module.finrank ℚ (generalBidegreeGridIndex A B → ℚ) =
      Module.finrank ℚ (generalBidegreeGrid A B → ℚ) := by
  rw [Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_congr (generalBidegreeGridPointEquiv A B)

/-- The evaluation map of the sheared monomial family is a linear
equivalence onto all rational functions on the grid. -/
noncomputable def generalBidegreeGridBasisEvaluationEquiv (A B : ℕ) :
    (generalBidegreeGridIndex A B → ℚ) ≃ₗ[ℚ]
      (generalBidegreeGrid A B → ℚ) :=
  LinearMap.linearEquivOfInjective (generalBidegreeGridBasisEvaluation A B)
    (generalBidegreeGridBasisEvaluation_injective A B)
    (finrank_generalBidegreeGridBasisEvaluation_source_eq_target A B)

/-- The basis evaluation equivalence has the advertised forward map. -/
@[simp] theorem generalBidegreeGridBasisEvaluationEquiv_apply (A B : ℕ)
    (c : generalBidegreeGridIndex A B → ℚ) :
    generalBidegreeGridBasisEvaluationEquiv A B c =
      generalBidegreeGridBasisEvaluation A B c :=
  rfl

/-- Evaluating the `ab`-th standard coordinate vector gives precisely the
`ab`-th sheared monomial basis function. -/
theorem generalBidegreeGridBasisEvaluation_basisFun (A B : ℕ)
    (ab : generalBidegreeGridIndex A B) :
    generalBidegreeGridBasisEvaluation A B
      ((Pi.basisFun ℚ (generalBidegreeGridIndex A B)) ab) =
        generalBidegreeGridBasisFunction A B ab := by
  ext p
  unfold generalBidegreeGridBasisEvaluation
  rw [Pi.basisFun_apply]
  simp [Pi.single_apply]

/-- The sheared-coordinate monomials are linearly independent as functions
on `Γ_{A,B}`. -/
theorem linearIndependent_generalBidegreeGridBasisFunction (A B : ℕ) :
    LinearIndependent ℚ (generalBidegreeGridBasisFunction A B) := by
  have hker : (generalBidegreeGridBasisEvaluation A B).ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective
      (generalBidegreeGridBasisEvaluation_injective A B)
  have h := (Pi.basisFun ℚ (generalBidegreeGridIndex A B)).linearIndependent.map'
    (generalBidegreeGridBasisEvaluation A B) hker
  change LinearIndependent ℚ
    (fun ab => generalBidegreeGridBasisEvaluation A B
      ((Pi.basisFun ℚ (generalBidegreeGridIndex A B)) ab)) at h
  have hfun :
      (fun ab => generalBidegreeGridBasisEvaluation A B
        ((Pi.basisFun ℚ (generalBidegreeGridIndex A B)) ab)) =
        generalBidegreeGridBasisFunction A B := by
    funext ab
    exact generalBidegreeGridBasisEvaluation_basisFun A B ab
  rw [hfun] at h
  exact h

/-- The sheared-coordinate monomials span every rational-valued function on
`Γ_{A,B}`. -/
theorem span_generalBidegreeGridBasisFunction_eq_top (A B : ℕ) :
    Submodule.span ℚ (Set.range (generalBidegreeGridBasisFunction A B)) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank
    (linearIndependent_generalBidegreeGridBasisFunction A B)
  calc
    Fintype.card (generalBidegreeGridIndex A B) =
        Fintype.card (generalBidegreeGrid A B) :=
      Fintype.card_congr (generalBidegreeGridPointEquiv A B)
    _ = Module.finrank ℚ (generalBidegreeGrid A B → ℚ) :=
      (Module.finrank_fintype_fun_eq_card ℚ).symm

end PellPaper
