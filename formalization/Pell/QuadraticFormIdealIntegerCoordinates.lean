import Pell.QuadraticAlgebraFieldDiscriminantEquality
import Pell.QuadraticFormIdealClassMap

/-!
# Integer coordinates in an attached form ideal

For a primitive form of positive fundamental discriminant, the actual
maximal-order ideal attached to the form has unique integer coordinates in
the ordered pair `a, -theta`, where `theta = (-b + sqrt D) / 2`.
The spanning argument uses the proved maximal-order coordinates and the
quadratic relation for `theta`.  No span or index hypothesis is supplied.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdealCoordinates_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem formIdealGenerator_coordinates (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (formIdealGenerator D Q hQ : rationalQuadraticAlgebra D) =
      ⟨-(Q.b : ℚ) / 2, 1 / 2⟩ := by
  rw [coe_formIdealGenerator]
  apply (div_eq_iff (by norm_num : (2 : rationalQuadraticAlgebra D) ≠ 0)).mpr
  ext <;> norm_num [show (2 : rationalQuadraticAlgebra D).re = 2 from rfl,
    show (2 : rationalQuadraticAlgebra D).im = 0 from rfl]

private theorem formIdealGenerator_square (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formIdealGenerator D Q hQ ^ 2 =
      -(Q.b : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        formIdealGenerator D Q hQ - Q.a * Q.c := by
  apply Subtype.ext
  change (formIdealGenerator D Q hQ : rationalQuadraticAlgebra D) ^ 2 =
    -(Q.b : rationalQuadraticAlgebra D) * formIdealGenerator D Q hQ - Q.a * Q.c
  rw [formIdealGenerator_coordinates]
  have hd : (Q.b : ℚ) ^ 2 - 4 * (Q.a : ℚ) * Q.c = D := by
    exact_mod_cast hQ
  ext <;> simp [pow_two]
  · nlinarith
  · ring

/-- Every algebraic integer is an integer linear combination of one and the
generator attached to a form of positive fundamental discriminant. -/
theorem ringOfIntegers_exists_int_coordinates_formIdealGenerator
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = (D : ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
    ∃ u v : ℤ, z = (u : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) +
      v * formIdealGenerator (D : ℤ) Q hQ := by
  have hparity : Even Q.b ↔ Even (D : ℤ) := by
    rw [← hQ]
    simp [discriminant, Int.even_sub, Int.even_pow,
      show Even (4 : ℤ) by decide]
  rcases hD.2 with hodd | ⟨d, hD, hdsq, hdmod⟩
  · obtain ⟨u, v, hu, hv⟩ :=
      rationalQuadraticAlgebra_integerCoordinates_of_squarefree_mod_four_one
        D hodd.1 hodd.2 z
    have hneven : ¬ Even (D : ℤ) := by
      rw [Int.even_iff]
      have hmod : (D : ℤ) % 4 = 1 := by exact_mod_cast hodd.2
      omega
    obtain ⟨k, hk⟩ := Int.even_add_one.mpr (fun hb => hneven (hparity.mp hb))
    have hkq : (Q.b : ℚ) + 1 = 2 * k := by
      have hk' : Q.b + 1 = 2 * k := by simpa [two_mul] using hk
      exact_mod_cast hk'
    refine ⟨u + k * v, v, ?_⟩
    apply Subtype.ext
    change (z : rationalQuadraticAlgebra (D : ℤ)) =
      ((u + k * v : ℤ) : rationalQuadraticAlgebra (D : ℤ)) +
        (v : rationalQuadraticAlgebra (D : ℤ)) * formIdealGenerator (D : ℤ) Q hQ
    rw [formIdealGenerator_coordinates]
    ext <;> norm_num
    · linear_combination -hu - hv / 2 + (v : ℚ) * hkq / 2
    · linear_combination -hv / 2
  · subst D
    obtain ⟨u, v, hu, hv⟩ :=
      rationalQuadraticAlgebra_integerCoordinates_of_four_mul_squarefree_mod_four
        d hdsq hdmod z
    have heven : Even Q.b := hparity.mpr ⟨(2 * d : ℕ), by push_cast; ring⟩
    obtain ⟨k, hk⟩ := heven
    have hkq : (Q.b : ℚ) = 2 * k := by
      have hk' : Q.b = 2 * k := by simpa [two_mul] using hk
      exact_mod_cast hk'
    refine ⟨u + k * v, v, ?_⟩
    apply Subtype.ext
    change (z : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) =
      ((u + k * v : ℤ) : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) +
        (v : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) *
          formIdealGenerator ((4 * d : ℕ) : ℤ) Q hQ
    rw [formIdealGenerator_coordinates]
    ext <;> norm_num
    · linear_combination -hu + (v : ℚ) * hkq / 2
    · linear_combination -hv / 2

/-- Membership in the actual attached ideal is equivalent to having integer
coordinates in the ordered pair `a, -theta`. -/
theorem mem_formAssociatedIdeal_iff_exists_int_coordinates
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = (D : ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
    z ∈ formAssociatedIdeal (D : ℤ) Q hQ ↔
      ∃ x y : ℤ, z =
        (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) * x -
          formIdealGenerator (D : ℤ) Q hQ * y := by
  let R := NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))
  let θ : R := formIdealGenerator (D : ℤ) Q hQ
  constructor
  · intro hz
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp hz
    obtain ⟨u, v, hr⟩ := ringOfIntegers_exists_int_coordinates_formIdealGenerator D hD Q hQ r
    obtain ⟨w, t, hs⟩ := ringOfIntegers_exists_int_coordinates_formIdealGenerator D hD Q hQ s
    refine ⟨u - t * Q.c, -(v * Q.a + w - t * Q.b), ?_⟩
    rw [← hrs, hr, hs]
    change ((u : R) + v * θ) * Q.a + ((w : R) + t * θ) * θ = _
    push_cast
    have hθ : θ ^ 2 = -(Q.b : R) * θ - Q.a * Q.c :=
      formIdealGenerator_square (D : ℤ) Q hQ
    linear_combination (t : R) * hθ
  · rintro ⟨x, y, rfl⟩
    exact Ideal.sub_mem _
      (Ideal.mul_mem_right _ _ (leadingCoefficient_mem_formAssociatedIdeal (D : ℤ) Q hQ))
      (Ideal.mul_mem_right _ _ (formIdealGenerator_mem_formAssociatedIdeal (D : ℤ) Q hQ))

/-- The two integer coordinates in `a, -theta` are unique when `a ≠ 0`. -/
theorem formAssociatedIdeal_int_coordinates_injective
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (ha : Q.a ≠ 0) :
    Function.Injective (fun p : ℤ × ℤ =>
      (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) * p.1 -
        formIdealGenerator D Q hQ * p.2) := by
  intro p q hpq
  have hfield := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) =>
      (z : rationalQuadraticAlgebra D)) hpq
  change (Q.a : rationalQuadraticAlgebra D) * p.1 - formIdealGenerator D Q hQ * p.2 =
    (Q.a : rationalQuadraticAlgebra D) * q.1 - formIdealGenerator D Q hQ * q.2 at hfield
  rw [formIdealGenerator_coordinates] at hfield
  have hre := congrArg QuadraticAlgebra.re hfield
  have him := congrArg QuadraticAlgebra.im hfield
  simp at hre him
  have hy : p.2 = q.2 := him
  have haq : (Q.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hxq : (p.1 : ℚ) = q.1 := by
    apply mul_left_cancel₀ haq
    rw [hy] at hre
    linarith
  exact Prod.ext (by exact_mod_cast hxq) hy

/-- Each element of a primitive form ideal at positive fundamental
discriminant has unique integer coordinates in `a, -theta`. -/
theorem formAssociatedIdeal_existsUnique_int_coordinates
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ z : formAssociatedIdeal (D : ℤ) Q.1 Q.2.2,
      ∃! p : ℤ × ℤ,
        z.1 = (Q.1.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) * p.1 -
          formIdealGenerator (D : ℤ) Q.1 Q.2.2 * p.2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro z
  obtain ⟨x, y, hxy⟩ :=
    (mem_formAssociatedIdeal_iff_exists_int_coordinates D hD Q.1 Q.2.2 z.1).mp z.2
  refine ⟨(x, y), hxy, ?_⟩
  intro p hp
  exact formAssociatedIdeal_int_coordinates_injective (D : ℤ) Q.1 Q.2.2
    (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q)
    (hp.symm.trans hxy)

end
end IntegralBinaryQuadraticForm
end PellPaper
