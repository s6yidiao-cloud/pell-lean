import Pell.RationalRankDefectRowBasis
import Pell.RationalRowMinorSelection
import Pell.FiniteEmbeddingExtraColumn
import Pell.IntegralKernelFromRationalRowSpan

/-!
# A bounded integral kernel from a rational rank defect

For an integral matrix with finitely many columns, a strict rank defect after
extension to `ℚ` supplies a row basis of size strictly below the number of
columns.  An invertible minor of that basis, together with one fresh column,
then gives an explicit integral cofactor kernel.  Rational row-combination
certificates transport it back to every original row.

The conclusion is deliberately finite and algebraic: it gives a nonzero
integral right-kernel vector and the real Hadamard coefficient bound for some
rank parameter `r`.  It does not assert a determinant-decay estimate, a
point-counting result, or an automatic source-specific choice of a rank
defect.
-/

namespace PellPaper

open scoped BigOperators EuclideanSpace

/-- A strict rank defect of the rationalization of a finite-column integral
matrix produces a nonzero integral right-kernel vector.  The existential
parameter `r` is the dimension of the rational row space; in particular it
is strictly smaller than the number of columns.  Under an entrywise bound by
the nonnegative integer `K`, every coefficient obeys the sharp real-valued
Hadamard bound `(sqrt r * K)^r`.

This is a finite linear-algebra bridge only.  In particular, it neither
derives the rank defect nor supplies the determinant or point-counting
estimates used elsewhere in the paper. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_rationalRank_lt_card_hadamard
    {ι κ : Type*} [Finite ι] [Fintype κ] (A : Matrix ι κ ℤ) {K : ℤ}
    (hrank : (A.map (algebraMap ℤ ℚ)).rank < Fintype.card κ)
    (hK : 0 ≤ K) (hbound : ∀ i j, |A i j| ≤ K) :
    ∃ r : ℕ, r < Fintype.card κ ∧ ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  classical
  obtain ⟨r, s, c, _hr, hrlt, _hs, hcombination, _hspan, hli⟩ :=
    exists_rationalRowBasisCertificate_of_rationalRank_lt_card A hrank
  let B : Matrix (Fin r) κ ℚ := (A.map (algebraMap ℤ ℚ)).submatrix s id
  have hBli : LinearIndependent ℚ B.row := by
    have hBrow : B.row = (A.map (algebraMap ℤ ℚ)).row ∘ s := by
      funext i j
      rfl
    rw [hBrow]
    exact hli
  obtain ⟨e0, he0det⟩ :=
    exists_injectiveColumnSelector_det_ne_zero_of_linearIndependent_rows B hBli
  let e : Fin r.succ ↪ κ := extendEmbeddingExtraColumn e0 hrlt
  let M : Matrix (Fin r) (Fin r) ℤ := A.submatrix s e0
  let b : Fin r → ℤ := fun i => A (s i) (extraColumn e0 hrlt)
  have hdet : M.det ≠ 0 := by
    intro hMdet
    apply he0det
    change ((A.map (algebraMap ℤ ℚ)).submatrix s e0).det = 0
    have hmap : (A.map (algebraMap ℤ ℚ)).submatrix s e0 =
        M.map (algebraMap ℤ ℚ) := by
      ext i j
      rfl
    rw [hmap]
    change ((algebraMap ℤ ℚ).mapMatrix M).det = 0
    rw [← RingHom.map_det, hMdet, map_zero]
  have hblock : A.submatrix s e = cofactorAugmentedMatrix M b := by
    ext i j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [e, b, cofactorAugmentedMatrix]
    · simp [e, M, cofactorAugmentedMatrix]
  have hM : ∀ i j, |M i j| ≤ K := by
    intro i j
    exact hbound (s i) (e0 j)
  have hb : ∀ i, |b i| ≤ K := by
    intro i
    exact hbound (s i) (extraColumn e0 hrlt)
  obtain ⟨z, hzne, hzero, hzbdd⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_selectedCofactorBlock_of_rationalRowCombination_hadamard
      A s c M b e hcombination hblock hdet hK hM hb
  exact ⟨r, hrlt, z, hzne, hzero, hzbdd⟩

end PellPaper
