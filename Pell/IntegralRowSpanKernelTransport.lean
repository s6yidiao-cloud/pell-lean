import Pell.IntegralSelectedCofactorKernel

/-!
# Transport of an integral right kernel through explicit row combinations

This module isolates the row-span step that is often used after a cofactor
kernel construction.  The hypothesis is deliberately concrete: every ambient
row is supplied as an integral linear combination of a fixed finite family of
selected rows.  A right-kernel vector for that selected-row submatrix is then
a right-kernel vector for the whole matrix.

No theorem here selects the rows, clears rational coefficients, or derives
the displayed integral row-combination certificate from a rank hypothesis.
-/

namespace PellPaper

open scoped BigOperators

/-- `c` is an explicit integral row-combination certificate for `A` from the
rows indexed by `s`.  The equality is coordinatewise so that no implicit
span/coercion convention is hidden in the hypothesis. -/
def HasIntegerRowCombination {ι κ : Type*} {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℤ) : Prop :=
  ∀ i j, A i j = ∑ k, c i k * A (s k) j

/-- An integral right-kernel vector of selected rows remains a right-kernel
vector of every row explicitly expressed as an integral combination of them.
This is a transport lemma only: it assumes the row-combination certificate. -/
theorem mulVec_eq_zero_of_integerRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℤ) (z : κ → ℤ)
    (hcombination : HasIntegerRowCombination A s c)
    (hselected : (A.submatrix s id).mulVec z = 0) :
    A.mulVec z = 0 := by
  classical
  funext i
  have hselectedCoordinate : ∀ k : Fin r, ∑ j, A (s k) j * z j = 0 := by
    intro k
    have hk := congr_fun hselected k
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using hk
  change ∑ j, A i j * z j = 0
  calc
    ∑ j, A i j * z j =
        ∑ j, (∑ k, c i k * A (s k) j) * z j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcombination i j]
    _ = ∑ k, c i k * (∑ j, A (s k) j * z j) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          simp [Finset.mul_sum, mul_assoc]
    _ = 0 := by simp [hselectedCoordinate]

/-- If selected columns of the selected-row submatrix equal `[M | b]`, its
zero-extended cofactor vector is a right-kernel vector of the full ambient
matrix once an explicit integral row-combination certificate is given. -/
theorem mulVec_selectedCofactorKernel_eq_zero_of_integerRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℤ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (hcombination : HasIntegerRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b) :
    A.mulVec (selectedCofactorKernel M b e) = 0 := by
  classical
  apply mulVec_eq_zero_of_integerRowCombination A s c
  · exact hcombination
  · apply mulVec_selectedCofactorKernel_eq_zero (A.submatrix s id) M b e
    ext i j
    change A (s i) (e j) = cofactorAugmentedMatrix M b i j
    exact congr_fun (congr_fun hblock i) j

/-- A nonsingular bounded cofactor block, selected columns, and an explicit
integral row-combination certificate give a nonzero bounded integral
right-kernel vector for the ambient matrix.  The bound is the existing
factorial/Leibniz cofactor bound; this result makes no pivot-selection,
row-selection, rational-clearing, or determinant-decay assertion. -/
theorem exists_nonzero_bounded_integral_kernel_of_selectedCofactorBlock_of_integerRowCombination
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℤ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    {K : ℤ} (hcombination : HasIntegerRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b)
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, |z j| ≤ (r.factorial : ℤ) * K ^ r := by
  classical
  refine ⟨selectedCofactorKernel M b e, selectedCofactorKernel_ne_zero M b e hdet,
    mulVec_selectedCofactorKernel_eq_zero_of_integerRowCombination
      A s c M b e hcombination hblock, ?_⟩
  exact abs_selectedCofactorKernel_le_factorial_mul_pow M b e hK hM hb

end PellPaper
