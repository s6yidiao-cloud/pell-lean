import Pell.RealQuadraticNumberFieldPositiveRadicand
import Mathlib.Data.Nat.Squarefree

/-!
# Squarefree normalization of an actual positive quadratic presentation

The existing natural-number squarefree decomposition is applied to a
positive integer radicand.  A nonzero square factor is removed by the proved
quadratic-algebra scaling equivalence.  Nonsquareness of the original
radicand forces the positive squarefree part to exceed one.

The final field theorem assumes only rational degree two and an explicit
real embedding, not a squarefree decomposition or a supplied presentation.
No fundamental-discriminant or isomorphism-class counting claim is made.
-/

namespace PellPaper

noncomputable section

/-- Any positive integer radicand with no rational square root has an
actually equivalent positive squarefree natural radicand greater than one. -/
theorem exists_squarefree_radicand_quadraticAlgebra_algEquiv
    (z : ℤ) (hz : 0 < z) (hns : ∀ r : ℚ, r ^ 2 ≠ (z : ℚ)) :
    ∃ d : ℕ, 1 < d ∧ Squarefree d ∧ (∀ r : ℚ, r ^ 2 ≠ (d : ℚ)) ∧
      Nonempty (QuadraticAlgebra ℚ (z : ℚ) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  have hn : 0 < z.toNat := by omega
  obtain ⟨d, s, hd, hs, hdecomp, hsquarefree⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hzNat : (z.toNat : ℚ) = (z : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hz.le
  have hdq : (z : ℚ) = (d : ℚ) * (s : ℚ) ^ 2 := by
    calc
      (z : ℚ) = (z.toNat : ℚ) := hzNat.symm
      _ = ((s ^ 2 * d : ℕ) : ℚ) := congrArg (fun n : ℕ => (n : ℚ)) hdecomp.symm
      _ = _ := by push_cast; ring
  have hdns : ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) := by
    intro r hr
    apply hns (r * s)
    rw [mul_pow, hr]
    exact hdq.symm
  have hd1 : 1 < d := by
    by_contra h
    have hdEq : d = 1 := by omega
    exact hdns 1 (by simp [hdEq])
  refine ⟨d, hd1, hsquarefree, hdns, ?_⟩
  rw [hdq]
  exact ⟨quadraticAlgebraScaleAlgEquiv d s (by exact_mod_cast hs.ne')⟩

/-- Every degree-two number field with an actual real embedding admits an
actual presentation with positive squarefree natural radicand greater than
one, without any caller-supplied decomposition or generator. -/
theorem exists_realQuadraticNumberField_squarefree_radicand
    (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℝ) :
    ∃ d : ℕ, 1 < d ∧ Squarefree d ∧ (∀ r : ℚ, r ^ 2 ≠ (d : ℚ)) ∧
      Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  obtain ⟨z, hz, hns, ⟨e⟩⟩ :=
    exists_realQuadraticNumberField_positive_integer_radicand K hK σ
  obtain ⟨d, hd, hsq, hdns, ⟨ed⟩⟩ :=
    exists_squarefree_radicand_quadraticAlgebra_algEquiv z hz hns
  exact ⟨d, hd, hsq, hdns, ⟨e.trans ed⟩⟩

end
end PellPaper
