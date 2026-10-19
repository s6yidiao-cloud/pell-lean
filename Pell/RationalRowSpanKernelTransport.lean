import Pell.IntegralRowSpanKernelTransport

/-!
# Transport of a rational right kernel through explicit rational row combinations

This module is the rational-coefficient analogue of
`IntegralRowSpanKernelTransport`.  It is useful when a row-span computation is
performed after passing an integral evaluation matrix to `ℚ`: an explicitly
given rational linear-combination certificate transports a right-kernel vector
of the selected rows to all rows.

The certificate is an assumption, not a rank theorem.  In particular, this
file does not select rows, manufacture rational coefficients, clear their
denominators, or make a determinant or counting assertion.
-/

namespace PellPaper

open scoped BigOperators

/-- `c` is an explicit rational row-combination certificate for the
rationalization of an integral matrix `A`, from the rows indexed by `s`.
The equality is coordinatewise, so no implicit span convention is hidden in
the hypothesis. -/
def HasRationalRowCombination {ι κ : Type*} {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℚ) : Prop :=
  ∀ i j, (A.map (algebraMap ℤ ℚ)) i j =
    ∑ k, c i k * (A.map (algebraMap ℤ ℚ)) (s k) j

/-- A rational right-kernel vector of selected rows remains a right-kernel
vector of every row explicitly expressed as a rational combination of them.
This is only a transport lemma: it assumes the rational row-combination
certificate. -/
theorem rational_mulVec_eq_zero_of_rationalRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℚ) (q : κ → ℚ)
    (hcombination : HasRationalRowCombination A s c)
    (hselected : ((A.map (algebraMap ℤ ℚ)).submatrix s id).mulVec q = 0) :
    (A.map (algebraMap ℤ ℚ)).mulVec q = 0 := by
  classical
  funext i
  have hselectedCoordinate : ∀ k : Fin r,
      ∑ j, (A.map (algebraMap ℤ ℚ)) (s k) j * q j = 0 := by
    intro k
    have hk := congr_fun hselected k
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using hk
  change ∑ j, (A.map (algebraMap ℤ ℚ)) i j * q j = 0
  calc
    ∑ j, (A.map (algebraMap ℤ ℚ)) i j * q j =
        ∑ j, (∑ k, c i k * (A.map (algebraMap ℤ ℚ)) (s k) j) * q j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcombination i j]
    _ = ∑ k, c i k *
        (∑ j, (A.map (algebraMap ℤ ℚ)) (s k) j * q j) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          simp [Finset.mul_sum, mul_assoc]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [hselectedCoordinate k]
          simp

/-- Casting the selected integral cofactor kernel to `ℚ` gives a rational
kernel of the selected rows whenever their selected columns form the
cofactor block. -/
theorem rational_mulVec_selectedCofactorKernel_eq_zero_of_selectedBlock
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b) :
    ((A.map (algebraMap ℤ ℚ)).submatrix s id).mulVec
        (fun j => (selectedCofactorKernel M b e j : ℚ)) = 0 := by
  classical
  have hintegral : (A.submatrix s id).mulVec (selectedCofactorKernel M b e) = 0 := by
    apply mulVec_selectedCofactorKernel_eq_zero (A.submatrix s id) M b e
    ext i j
    change A (s i) (e j) = cofactorAugmentedMatrix M b i j
    exact congr_fun (congr_fun hblock i) j
  funext i
  have hsubmatrix :
      (A.map (algebraMap ℤ ℚ)).submatrix s id =
        (A.submatrix s id).map (algebraMap ℤ ℚ) := by
    rfl
  rw [hsubmatrix]
  have hmap := RingHom.map_mulVec (algebraMap ℤ ℚ) (A.submatrix s id)
    (selectedCofactorKernel M b e) i
  rw [hintegral] at hmap
  simpa [Function.comp_def] using hmap.symm

/-- An explicit rational row-combination certificate propagates the rational
cofactor kernel from selected rows to every row of the ambient integral
matrix.  This does not claim that such a certificate exists or that its
denominators have been cleared. -/
theorem rational_mulVec_selectedCofactorKernel_eq_zero_of_rationalRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℚ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (hcombination : HasRationalRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b) :
    (A.map (algebraMap ℤ ℚ)).mulVec
        (fun j => (selectedCofactorKernel M b e j : ℚ)) = 0 := by
  apply rational_mulVec_eq_zero_of_rationalRowCombination A s c
  · exact hcombination
  · exact rational_mulVec_selectedCofactorKernel_eq_zero_of_selectedBlock
      A s M b e hblock

/-- If the cofactor block is nonsingular, its zero-extended integral kernel
remains nonzero after casting to `ℚ`; combined with an explicit rational
row-combination certificate, this gives a nonzero rational right-kernel
vector of the ambient matrix. -/
theorem exists_nonzero_rational_kernel_of_selectedCofactorBlock_of_rationalRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℚ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (hcombination : HasRationalRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b)
    (hdet : M.det ≠ 0) :
    ∃ q : κ → ℚ, q ≠ 0 ∧ (A.map (algebraMap ℤ ℚ)).mulVec q = 0 := by
  let z : κ → ℤ := selectedCofactorKernel M b e
  refine ⟨fun j => (z j : ℚ), ?_, ?_⟩
  · intro hq
    apply selectedCofactorKernel_ne_zero M b e hdet
    funext j
    apply Rat.intCast_injective
    simpa [z] using congr_fun hq j
  · simpa [z] using
      rational_mulVec_selectedCofactorKernel_eq_zero_of_rationalRowCombination
        A s c M b e hcombination hblock

end PellPaper
