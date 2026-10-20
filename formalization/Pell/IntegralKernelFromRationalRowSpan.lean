import Pell.RationalRowSpanKernelTransport
import Pell.IntegralSelectedCofactorKernelHadamard

/-!
# Integral cofactor kernels from rational row-span certificates

An explicit rational row-combination certificate can be used to transport the
zero-extended integral cofactor vector through all rows of an integral matrix.
The transport first happens after scalar extension to `ℚ`, using
`RationalRowSpanKernelTransport`; injectivity of `ℤ → ℚ` then reflects the
coordinatewise zero relation back to `ℤ`.

The certificate, selected augmented block, and nonsingularity hypothesis all
remain explicit.  This module neither selects rows or columns automatically,
nor proves a determinant-decay or counting estimate.
-/

namespace PellPaper

open scoped BigOperators EuclideanSpace

/-- The zero-extended integral cofactor vector is a right-kernel vector of an
integral matrix when every row is supplied as a rational linear combination of
the selected rows.  The rational certificate is used only after casting to
`ℚ`; injectivity of the integer cast reflects the resulting relation to `ℤ`. -/
theorem mulVec_selectedCofactorKernel_eq_zero_of_rationalRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℚ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (hcombination : HasRationalRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b) :
    A.mulVec (selectedCofactorKernel M b e) = 0 := by
  classical
  funext i
  apply Rat.intCast_injective
  have hrat :=
    rational_mulVec_selectedCofactorKernel_eq_zero_of_rationalRowCombination
      A s c M b e hcombination hblock
  have hcoordinate := congr_fun hrat i
  have hcast := RingHom.map_mulVec (algebraMap ℤ ℚ) A
    (selectedCofactorKernel M b e) i
  have hcastZero :
      (algebraMap ℤ ℚ) (A.mulVec (selectedCofactorKernel M b e) i) = 0 := by
    calc
      (algebraMap ℤ ℚ) (A.mulVec (selectedCofactorKernel M b e) i) =
          (A.map (algebraMap ℤ ℚ)).mulVec
            ((algebraMap ℤ ℚ) ∘ selectedCofactorKernel M b e) i := hcast
      _ = 0 := by simpa [Function.comp_def] using hcoordinate
  simpa using hcastZero

/-- A nonsingular selected integral cofactor block, an explicit rational
row-combination certificate, and entrywise bounds supply a nonzero integral
right-kernel vector of the full matrix with the sharp Hadamard bound.  The
bound is real-valued to retain the exact factor `sqrt r`; no automatic pivot
selection or determinant/counting estimate is asserted. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_selectedCofactorBlock_of_rationalRowCombination_hadamard
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℚ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    {K : ℤ} (hcombination : HasRationalRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b)
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  classical
  refine ⟨selectedCofactorKernel M b e, selectedCofactorKernel_ne_zero M b e hdet,
    mulVec_selectedCofactorKernel_eq_zero_of_rationalRowCombination
      A s c M b e hcombination hblock, ?_⟩
  exact abs_selectedCofactorKernel_le_hadamard M b e hK hM hb

end PellPaper
