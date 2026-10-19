import Pell.RealQuadraticFieldFundamentalBijection
import Pell.GenuineQuadraticAlgebraClassNumberModel

/-!
# The literal finite class-number sum over real quadratic fields

The finite cutoff contains actual field isomorphism classes. Its membership
criterion is the strict bound on the actual field discriminant, proved from
the field classification. The finite sum uses the actual ideal class number,
and is then proved equal to the genuine discriminant-indexed model sum.
-/

namespace PellPaper

noncomputable section

/-- Actual field classes with field discriminant strictly below the real cutoff. -/
def realQuadraticFieldClassesBelow (X : ℝ) : Finset RealQuadraticFieldClass := by
  classical
  exact ((fundamentalDiscriminantsBelow X).subtype PositiveFundamentalDiscriminant).map
    positiveFundamentalFieldClassEquiv.toEmbedding

theorem mem_realQuadraticFieldClassesBelow (X : ℝ) (c : RealQuadraticFieldClass) :
    c ∈ realQuadraticFieldClassesBelow X ↔
      (realQuadraticFieldClassDiscriminant c : ℝ) < X := by
  classical
  obtain ⟨D, rfl⟩ := positiveFundamentalToRealQuadraticFieldClass_surjective c
  simp only [realQuadraticFieldClassesBelow, Finset.mem_map]
  constructor
  · rintro ⟨E, hE, heq⟩
    have hED : E = D :=
      positiveFundamentalToRealQuadraticFieldClass_injective heq
    subst E
    rw [realQuadraticFieldClassDiscriminant_positiveFundamental]
    exact_mod_cast (mem_fundamentalDiscriminantsBelow.mp (Finset.mem_subtype.mp hE)).2
  · intro hD
    refine ⟨D, Finset.mem_subtype.mpr ?_, rfl⟩
    apply mem_fundamentalDiscriminantsBelow.mpr
    refine ⟨D.property, ?_⟩
    rw [realQuadraticFieldClassDiscriminant_positiveFundamental] at hD
    exact_mod_cast hD

/-- Every class in this actual real-field family has positive field discriminant. -/
theorem realQuadraticFieldClassDiscriminant_pos (c : RealQuadraticFieldClass) :
    0 < realQuadraticFieldClassDiscriminant c := by
  obtain ⟨D, rfl⟩ := positiveFundamentalToRealQuadraticFieldClass_surjective c
  rw [realQuadraticFieldClassDiscriminant_positiveFundamental]
  exact_mod_cast (lt_trans Nat.zero_lt_one D.property.1)

theorem mem_realQuadraticFieldClassesBelow_iff_positive_discriminant
    (X : ℝ) (c : RealQuadraticFieldClass) :
    c ∈ realQuadraticFieldClassesBelow X ↔
      0 < realQuadraticFieldClassDiscriminant c ∧
        (realQuadraticFieldClassDiscriminant c : ℝ) < X := by
  rw [mem_realQuadraticFieldClassesBelow]
  exact (and_iff_right (realQuadraticFieldClassDiscriminant_pos c)).symm

/-- The finite sum of actual ordinary ideal class numbers, each field class once. -/
def realQuadraticFieldClassSum (X : ℝ) : ℝ :=
  ∑ c ∈ realQuadraticFieldClassesBelow X, (realQuadraticFieldClassNumber c : ℝ)

/-- Identification of the literal field sum with the genuine model's ordinary sum. -/
theorem realQuadraticFieldClassSum_eq_genuine_ordinaryClassSum (X : ℝ) :
    realQuadraticFieldClassSum X =
      genuineQuadraticAlgebraClassNumberModel.ordinaryClassSum X := by
  classical
  unfold realQuadraticFieldClassSum realQuadraticFieldClassesBelow
  rw [Finset.sum_map]
  calc
    (∑ D ∈ (fundamentalDiscriminantsBelow X).subtype PositiveFundamentalDiscriminant,
        (realQuadraticFieldClassNumber (positiveFundamentalFieldClassEquiv D) : ℝ)) =
      ∑ D ∈ (fundamentalDiscriminantsBelow X).subtype PositiveFundamentalDiscriminant,
        (genuineQuadraticAlgebraClassNumberModel.ordinaryClassNumber D.val : ℝ) := by
      apply Finset.sum_congr rfl
      intro D _hD
      change (realQuadraticFieldClassNumber (positiveFundamentalToRealQuadraticFieldClass D) : ℝ) = _
      rw [realQuadraticFieldClassNumber_positiveFundamental,
        genuineQuadraticAlgebraClassNumberModel_ordinary_eq D.property]
    _ = genuineQuadraticAlgebraClassNumberModel.ordinaryClassSum X := by
      unfold ClassNumberModel.ordinaryClassSum
      exact Finset.sum_subtype_of_mem
        (fun D : ℕ => (genuineQuadraticAlgebraClassNumberModel.ordinaryClassNumber D : ℝ))
        (fun D hD => (mem_fundamentalDiscriminantsBelow.mp hD).1)

/-- The first displayed inequality of the field-average theorem, for actual
field classes and the literal proper primitive form quotient. No analytic
estimate, arbitrary class-number model, or field-classification input remains. -/
theorem realQuadraticFieldClassSum_le_properFormClassSum (X : ℝ) :
    realQuadraticFieldClassSum X ≤
      ∑ D ∈ fundamentalDiscriminantsBelow X,
        (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ) := by
  rw [realQuadraticFieldClassSum_eq_genuine_ordinaryClassSum,
    ← genuineQuadraticAlgebraClassNumberModel_formClassSum_eq]
  exact genuineQuadraticAlgebraClassNumberModel.ordinaryClassSum_le_formClassSum X

end
end PellPaper
