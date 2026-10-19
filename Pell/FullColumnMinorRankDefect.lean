import Pell.FullColumnMinorKernel

/-!
# Rank defect from vanishing full-column minors

This module turns the right-kernel conclusion of
`FullColumnMinorKernel` into the strict matrix-rank inequality needed by
the bounded cofactor construction.  It is deliberately a finite rational
linear-algebra statement: no determinant estimate is proved here.

The row selectors are embeddings.  Consequently, when there are fewer rows
than columns there need not be any selector, the minor hypothesis is
vacuous, and the conclusion correctly says that the rank is strictly below
the number of columns.  When the column type is empty, the hypothesis is in
fact inconsistent (the unique empty minor has determinant one); the theorem
still has its expected empty-column conclusion.
-/

namespace PellPaper

/-- If every square minor using all columns of a finite rational matrix has
zero determinant, then its rank is strictly smaller than its number of
columns.  This includes the case of too few rows, where the quantified
minor condition is vacuous. -/
theorem rationalRank_lt_card_of_forall_fullColumnMinors_eq_zero
    {ι κ : Type*} [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ)
    (hminor : ∀ r : κ ↪ ι, (A.submatrix r id).det = 0) :
    A.rank < Fintype.card κ := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨q, hqne, hqzero⟩ :=
    exists_rational_kernel_of_forall_fullColumnMinors_eq_zero A hminor
  have hqker : q ∈ LinearMap.ker A.mulVecLin := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hqzero
  have hker_ne : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro hbot
    have hqzero' : q = 0 := by
      rw [hbot] at hqker
      simpa using hqker
    exact hqne hqzero'
  have hker_pos : 0 < Module.finrank ℚ (LinearMap.ker A.mulVecLin) :=
    lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.mpr hker_ne)
  have hsum : A.rank + Module.finrank ℚ (LinearMap.ker A.mulVecLin) =
      Fintype.card κ := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_add_finrank_ker A.mulVecLin)
  omega

/-- The same rank-defect bridge when the vanishing minors are already stated
after extending an integral matrix to `ℚ`. -/
theorem rationalRank_lt_card_of_forall_fullColumnMinors_map_eq_zero
    {ι κ : Type*} [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℤ)
    (hminor : ∀ r : κ ↪ ι,
      (((A.map (algebraMap ℤ ℚ)).submatrix r id).det = 0)) :
    (A.map (algebraMap ℤ ℚ)).rank < Fintype.card κ :=
  rationalRank_lt_card_of_forall_fullColumnMinors_eq_zero
    (A.map (algebraMap ℤ ℚ)) hminor

/-- If every full-column minor of a finite integral matrix vanishes over
`ℤ`, then its rationalization has rank strictly smaller than its number of
columns. -/
theorem rationalRank_lt_card_of_forall_fullIntegralColumnMinors_eq_zero
    {ι κ : Type*} [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℤ)
    (hminor : ∀ r : κ ↪ ι, (A.submatrix r id).det = 0) :
    (A.map (algebraMap ℤ ℚ)).rank < Fintype.card κ := by
  apply rationalRank_lt_card_of_forall_fullColumnMinors_map_eq_zero A
  intro r
  rw [Matrix.submatrix_map]
  change ((algebraMap ℤ ℚ).mapMatrix ((A.submatrix r id))).det = 0
  rw [← RingHom.map_det, hminor r, map_zero]

end PellPaper
