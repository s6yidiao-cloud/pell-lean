import Pell.RealQuadraticNumberFieldSquarefreeRadicand
import Pell.ClassAverage
import Pell.QuadraticOrderPellEmbedding

/-!
# Actual positive-fundamental presentations of real quadratic number fields

A positive squarefree natural radicand greater than one determines a
positive fundamental index: use the radicand itself in residue class one
modulo four, and four times the radicand otherwise.  In the latter branch,
the previously proved scaling equivalence rescales the generator by two.

Composing with squarefree normalization yields an actual rational-algebra
equivalence for every degree-two number field admitting a real embedding.
Discriminant invariance, uniqueness of the index, and counting of field
isomorphism classes are separate statements and are not asserted here.
-/

namespace PellPaper

noncomputable section

/-- The usual index attached to a positive squarefree radicand greater than
one satisfies the project's arithmetic fundamental-discriminant predicate. -/
theorem positiveFundamentalDiscriminant_squarefree_index
    (d : ℕ) (hd : 1 < d) (hsq : Squarefree d) :
    PositiveFundamentalDiscriminant (if d % 4 = 1 then d else 4 * d) := by
  by_cases hmod : d % 4 = 1
  · simp only [if_pos hmod]
    exact ⟨hd, Or.inl ⟨hsq, hmod⟩⟩
  · simp only [if_neg hmod]
    have hmod0 : d % 4 ≠ 0 := by
      intro h
      have hdiv : 4 ∣ d := Nat.dvd_of_mod_eq_zero h
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two)
        (by simpa using hdiv)
    have hmod4 : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
    refine ⟨by omega, Or.inr ⟨d, rfl, hsq, ?_⟩⟩
    omega

/-- Changing a squarefree radicand to its positive fundamental index is
realized by an actual rational-algebra equivalence, not merely a numerical
relation between the two indices. -/
theorem squarefree_radicand_fundamental_index_algEquiv
    (d : ℕ) :
    Nonempty (QuadraticAlgebra ℚ (d : ℚ) 0 ≃ₐ[ℚ]
      rationalQuadraticAlgebra ((if d % 4 = 1 then d else 4 * d : ℕ) : ℤ)) := by
  by_cases hmod : d % 4 = 1
  · rw [if_pos hmod]
    exact ⟨AlgEquiv.refl⟩
  · rw [if_neg hmod]
    have hscale : (((4 * d : ℕ) : ℤ) : ℚ) = (d : ℚ) * (2 : ℚ) ^ 2 := by
      push_cast
      ring
    change Nonempty (QuadraticAlgebra ℚ (d : ℚ) 0 ≃ₐ[ℚ]
      QuadraticAlgebra ℚ (((4 * d : ℕ) : ℤ) : ℚ) 0)
    rw [hscale]
    exact ⟨(quadraticAlgebraScaleAlgEquiv d 2 (by norm_num)).symm⟩

/-- Every degree-two number field with an explicit real embedding is
actually equivalent to the concrete quadratic algebra at a positive
fundamental index; no generator, decomposition, or index is supplied. -/
theorem exists_realQuadraticNumberField_positiveFundamental_presentation
    (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℝ) :
    ∃ D : ℕ, PositiveFundamentalDiscriminant D ∧
      Nonempty (K ≃ₐ[ℚ] rationalQuadraticAlgebra (D : ℤ)) := by
  obtain ⟨d, hd, hsq, _, ⟨e⟩⟩ :=
    exists_realQuadraticNumberField_squarefree_radicand K hK σ
  obtain ⟨ed⟩ := squarefree_radicand_fundamental_index_algEquiv d
  exact ⟨if d % 4 = 1 then d else 4 * d,
    positiveFundamentalDiscriminant_squarefree_index d hd hsq, ⟨e.trans ed⟩⟩

end
end PellPaper
