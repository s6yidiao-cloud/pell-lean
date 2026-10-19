import Pell.QuadraticOrderFormLatticeIndex
import Pell.QuadraticFieldInvariantTransport
import Pell.QuadraticFormWideClassSurjectivity

/-!
# The maximal-order wide class number along a square conductor

The quadratic algebras with radicands `D₀ f²` and `D₀` are rationally
algebra-equivalent when `f > 0`.  Transporting rings of integers and their
actual wide class groups shows that the former class group has the ordinary
class number at the positive fundamental index `D₀`.  Consequently it is
bounded by the already established proper-form class count at `D₀`.

This is only maximal-order class-number transport.  It makes no assertion
about fibres of forms of discriminant `D₀ f²` or about nonmaximal-order
class numbers.
-/

namespace PellPaper

noncomputable section

private def rationalQuadraticAlgebraNatMulSqAlgEquiv
    (D₀ f : ℕ) (hf : 0 < f) :
    rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ)) ≃ₐ[ℚ]
      rationalQuadraticAlgebra (D₀ : ℤ) := by
  have hfq : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  refine
    { toFun := fun z => ⟨z.re, (f : ℚ) * z.im⟩
      invFun := fun z => ⟨z.re, z.im / (f : ℚ)⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · intro z
    ext <;> simp
    field_simp [hfq]
  · intro z
    ext <;> simp
    field_simp [hfq]
  · intro z w
    ext <;> simp <;> ring
  · intro z w
    ext <;> simp
    ring
  · intro r
    ext <;> simp

local instance rationalQuadraticAlgebra_orderWideClassNumber_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The actual wide class group at radicand `D₀ f²` has cardinality equal
to the ordinary class number at the fundamental radicand `D₀`. -/
theorem natCard_classGroup_rationalQuadraticAlgebra_nat_mul_sq_eq
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    let _ : Fact
        (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
    Nat.card
        (ClassGroup (NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ))))) =
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D₀ hD₀ := by
  let _ : Fact
      (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D₀ : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD₀⟩
  dsimp only
  have hclass := numberFieldClassNumber_eq_of_algEquiv
    (rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ)))
    (rationalQuadraticAlgebra (D₀ : ℤ))
    (rationalQuadraticAlgebraNatMulSqAlgEquiv D₀ f hf)
  simpa only [rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant,
    rationalQuadraticAlgebraClassNumber, NumberField.classNumber,
    Nat.card_eq_fintype_card] using hclass

/-- The same actual wide class group cardinality is bounded by the genuine
proper-form class count at the fundamental discriminant. -/
theorem natCard_classGroup_rationalQuadraticAlgebra_nat_mul_sq_le_properFormClass_card
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    let _ : Fact
        (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
    Nat.card
        (ClassGroup (NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ))))) ≤
      Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D₀ : ℤ)) := by
  let _ : Fact
      (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
  dsimp only
  rw [natCard_classGroup_rationalQuadraticAlgebra_nat_mul_sq_eq D₀ f hD₀ hf]
  exact IntegralBinaryQuadraticForm.classNumber_le_properFormClass_card D₀ hD₀

end
end PellPaper
