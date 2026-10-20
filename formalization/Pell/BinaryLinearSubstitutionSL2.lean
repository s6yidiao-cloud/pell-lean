import Pell.BinaryLinearSubstitutionHeight
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Evaluation and cancellation for binary substitutions by integral `SL₂`

The coefficient-height module defines the row convention for a binary
linear substitution.  This file records its exact semantic action:
evaluating the transformed polynomial at `x` is evaluation of the original
polynomial at `W.mulVec x`.  It also proves the corresponding composition
law and uses the genuine inverse in `SL(2, ℤ)` to show that substitution by
an integral determinant-one matrix is injective and hence preserves
nonzero polynomials.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- Exact evaluation identity for the row convention used by
`binaryLinearSubstitution`. -/
@[simp]
theorem eval_binaryLinearSubstitution
    (W : Matrix (Fin 2) (Fin 2) ℤ)
    (K : MvPolynomial (Fin 2) ℤ) (x : Fin 2 → ℤ) :
    MvPolynomial.eval x (binaryLinearSubstitution W K) =
      MvPolynomial.eval (W.mulVec x) K := by
  rw [binaryLinearSubstitution]
  change MvPolynomial.eval x
      (MvPolynomial.eval₂ MvPolynomial.C (binaryLinearSubstitutionForm W) K) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun y : Fin 2 → ℤ => MvPolynomial.eval y K)
  funext i
  simp [binaryLinearSubstitutionForm, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- Applying first `W` and then `V` to the variables is substitution by
the matrix product `W * V`.  The order follows the row convention:
`K(W(Vx)) = K((W * V)x)`. -/
theorem binaryLinearSubstitution_comp_apply
    (W V : Matrix (Fin 2) (Fin 2) ℤ)
    (K : MvPolynomial (Fin 2) ℤ) :
    binaryLinearSubstitution V (binaryLinearSubstitution W K) =
      binaryLinearSubstitution (W * V) K := by
  rw [binaryLinearSubstitution, binaryLinearSubstitution,
    MvPolynomial.bind₁_bind₁]
  change MvPolynomial.bind₁
      (fun i => MvPolynomial.bind₁ (binaryLinearSubstitutionForm V)
        (binaryLinearSubstitutionForm W i)) K =
    MvPolynomial.bind₁ (binaryLinearSubstitutionForm (W * V)) K
  apply congrArg (fun f : Fin 2 → MvPolynomial (Fin 2) ℤ =>
    MvPolynomial.bind₁ f K)
  funext i
  simp [binaryLinearSubstitutionForm, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The identity matrix induces the identity binary substitution. -/
@[simp]
theorem binaryLinearSubstitution_one (K : MvPolynomial (Fin 2) ℤ) :
    binaryLinearSubstitution (1 : Matrix (Fin 2) (Fin 2) ℤ) K = K := by
  rw [binaryLinearSubstitution]
  have hforms : binaryLinearSubstitutionForm
      (1 : Matrix (Fin 2) (Fin 2) ℤ) = MvPolynomial.X := by
    funext i
    fin_cases i <;> simp [binaryLinearSubstitutionForm, Matrix.one_apply]
  rw [hforms]
  exact AlgHom.congr_fun MvPolynomial.bind₁_X_left K

/-- Substitution by the inverse of an integral determinant-one matrix is a
left inverse to substitution by that matrix. -/
@[simp]
theorem binaryLinearSubstitution_sl2_inverse_left
    (W : SL(2, ℤ)) (K : MvPolynomial (Fin 2) ℤ) :
    binaryLinearSubstitution ((W⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        (binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K) = K := by
  rw [binaryLinearSubstitution_comp_apply]
  have hmat : (W : Matrix (Fin 2) (Fin 2) ℤ) *
      ((W⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    change ((W * W⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    rw [mul_inv_cancel]
  rw [hmat, binaryLinearSubstitution_one]

/-- Binary substitution by an integral determinant-one matrix is
injective. -/
theorem binaryLinearSubstitution_sl2_injective (W : SL(2, ℤ)) :
    Function.Injective
      (binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro K L h
  have h' := congrArg
    (binaryLinearSubstitution
      ((W⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h
  calc
    K = binaryLinearSubstitution
        ((W⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          (binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K) :=
      (binaryLinearSubstitution_sl2_inverse_left W K).symm
    _ = binaryLinearSubstitution
        ((W⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          (binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) L) := h'
    _ = L := binaryLinearSubstitution_sl2_inverse_left W L

/-- In particular, an integral determinant-one change of variables cannot
turn a nonzero polynomial into the zero polynomial. -/
theorem binaryLinearSubstitution_sl2_ne_zero
    (W : SL(2, ℤ)) {K : MvPolynomial (Fin 2) ℤ} (hK : K ≠ 0) :
    binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K ≠ 0 := by
  exact (binaryLinearSubstitution_sl2_injective W).ne hK

end
end PellPaper
