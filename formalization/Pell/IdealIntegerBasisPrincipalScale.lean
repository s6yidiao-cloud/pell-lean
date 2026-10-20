import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Operations

/-!
# Principal scaling from corresponding integer ideal bases

A finite integer basis of an ideal generates that same ideal over its
ambient commutative ring.  Consequently, equal scaled basis vectors give
equal principal-scaled ideals.  No domain, nonzero-ideal, or nonzero-scalar
assumption is required; the canonical integer scalar action suffices.
-/

namespace PellPaper

noncomputable section

/-- An actual finite integer ideal basis generates the ideal over the
ambient ring, not merely over the integers. -/
theorem ideal_span_range_integerBasis
    {A ι : Type*} [CommRing A] [Fintype ι]
    (I : Ideal A) (bI : Module.Basis ι ℤ I) :
    Ideal.span (Set.range (fun i => (bI i : A))) = I := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (bI i).2
  · intro z hz
    have hsum := congrArg (fun w : I => (w : A)) (bI.sum_repr ⟨z, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hsum
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    rw [zsmul_eq_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Matching scalar multiples of corresponding integer basis vectors
force equality of the actual principal-scaled ideals, even for zero scalars. -/
theorem ideal_principalScale_eq_of_integerBasis_scale
    {A ι : Type*} [CommRing A] [Fintype ι]
    (I J : Ideal A) (bI : Module.Basis ι ℤ I) (bJ : Module.Basis ι ℤ J)
    (c d : A) (hscale : ∀ i, c * (bI i : A) = d * (bJ i : A)) :
    Ideal.span {c} * I = Ideal.span {d} * J := by
  rw [← ideal_span_range_integerBasis I bI, ← ideal_span_range_integerBasis J bJ,
    Ideal.span_mul_span, Ideal.span_mul_span]
  congr 1
  simp only [Set.singleton_mul, ← Set.range_comp]
  exact congrArg Set.range (funext hscale)

end

end PellPaper
