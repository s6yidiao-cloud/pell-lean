import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Rank defect from vanishing full-column minors

For a finite matrix over a field, if every square submatrix using all columns
has zero determinant, then the original matrix has a nonzero vector in its
right kernel.  We quantify over injective row selectors, so each tested
submatrix is genuinely a full-column minor; a hypothetical full-rank matrix
constructs the required selector automatically.
-/

namespace PellPaper

/-- Vanishing of every square submatrix formed from all columns forces a
nonzero rational right-kernel vector. -/
theorem exists_rational_kernel_of_forall_fullColumnMinors_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ)
    (hminor : ∀ r : κ ↪ ι, (A.submatrix r id).det = 0) :
    ∃ q : κ → ℚ, q ≠ 0 ∧ A.mulVec q = 0 := by
  classical
  by_contra hkernel
  push Not at hkernel
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hxy'
    exact hkernel (x - y) (sub_ne_zero.mpr hxy') (by
      rw [Matrix.mulVec_sub, hxy, sub_self])
  have hrank : A.rank = Fintype.card κ := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj,
      Module.finrank_fintype_fun_eq_card]
  obtain ⟨f, hfmem, -, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.row)
  have hfinrank : Module.finrank ℚ (Submodule.span ℚ (Set.range A.row)) = Fintype.card κ := by
    rw [← A.rank_eq_finrank_span_row, hrank]
  let e : κ ≃ Fin (Module.finrank ℚ (Submodule.span ℚ (Set.range A.row))) :=
    Fintype.equivFinOfCardEq hfinrank.symm
  choose r hr using hfmem
  have hrinj : Function.Injective r := by
    intro i j hij
    apply hfli.injective
    rw [← hr i, ← hr j, hij]
  let B : Matrix κ κ ℚ :=
    A.submatrix (r ∘ e) id
  have hBrow : B.row = f ∘ e := by
    funext i
    ext j
    change A (r (e i)) j = f (e i) j
    exact congr_fun (hr (e i)) j
  have hBli : LinearIndependent ℚ B.row := by
    rw [hBrow]
    exact hfli.comp e e.injective
  have hBdet : B.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hvne, hvzero⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    exact hvne ((Matrix.vecMul_injective_iff.mpr hBli) (by simpa using hvzero))
  exact hBdet (hminor ⟨r ∘ e, hrinj.comp e.injective⟩)

/-- In particular, vanishing of all full-column minors makes the rectangular
matrix map noninjective.  The preceding theorem contains the substantive
finite-rank argument; this corollary presents the rank defect in the form
used by the evaluation-matrix bridge. -/
theorem not_injective_mulVec_of_forall_fullColumnMinors_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ)
    (hminor : ∀ r : κ ↪ ι, (A.submatrix r id).det = 0) :
    ¬ Function.Injective A.mulVec := by
  intro hinj
  obtain ⟨q, hqne, hqzero⟩ :=
    exists_rational_kernel_of_forall_fullColumnMinors_eq_zero A hminor
  apply hqne
  apply hinj
  simpa using hqzero

end PellPaper
