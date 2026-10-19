import Pell.FullColumnMinorKernel

/-!
# A nonsingular minor from independent rational rows

For a finite rational matrix, linearly independent rows admit a square minor
with nonzero determinant.  The proof is the contrapositive of the existing
full-column-minor kernel lemma, applied to the transpose.

This is only a finite linear-algebra selection result.  It neither selects an
additional column for a cofactor construction nor makes a rank, height, or
determinant-decay assertion.
-/

namespace PellPaper

/-- If all `r` rows of a finite rational matrix are linearly independent,
some injectively selected family of `r` columns gives a nonsingular square
minor. -/
theorem exists_injectiveColumnSelector_det_ne_zero_of_linearIndependent_rows
    {r : ℕ} {κ : Type*} [Fintype κ]
    (B : Matrix (Fin r) κ ℚ) (hrows : LinearIndependent ℚ B.row) :
    ∃ e : Fin r ↪ κ, (B.submatrix id e).det ≠ 0 := by
  classical
  by_contra hselector
  push Not at hselector
  have hminor : ∀ e : Fin r ↪ κ, ((B.transpose).submatrix e id).det = 0 := by
    intro e
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    exact hselector e
  obtain ⟨q, hqne, hqzero⟩ :=
    exists_rational_kernel_of_forall_fullColumnMinors_eq_zero B.transpose hminor
  apply hqne
  apply Matrix.vecMul_injective_iff.mpr hrows
  have hvec : Matrix.vecMul q B = 0 := by
    rw [← Matrix.mulVec_transpose]
    exact hqzero
  simpa using hvec

end PellPaper
