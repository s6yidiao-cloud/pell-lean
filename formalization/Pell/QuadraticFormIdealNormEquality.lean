import Pell.QuadraticFormIdealNormBridge
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Norm equality for a primitive form ideal

For a primitive integral form of nonsquare discriminant `D`, conjugation gives
`I * conjugate I = (a)`.  The product contains `a²`, `ab`, and `ac`, so the
reverse containment follows from integer Bézout.  Conjugation induces a ring
equivalence of quotients, hence preserves absolute ideal norm.  Taking norms
of the product identity proves `absNorm I = |a|`.

This statement uses the actual maximal-order ideal from
`QuadraticFormIdealAttachment`; it does not require a fundamental discriminant
or an explicit description of an integral basis.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdealNormEquality_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private def quadraticConjugationAlgEquiv (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    rationalQuadraticAlgebra D ≃ₐ[ℤ] rationalQuadraticAlgebra D :=
  { toRingEquiv := starRingAut
    commutes' := by intro z; simp }

/-- Quadratic conjugation restricts to a ring automorphism of the actual
ring of integers, since it preserves integrality over `ℤ`. -/
def ringOfIntegersQuadraticConjugation (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) ≃+*
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D) where
  toFun x := ⟨quadraticConjugationAlgEquiv D (x : rationalQuadraticAlgebra D),
    IsIntegral.map (quadraticConjugationAlgEquiv D) x.2⟩
  invFun x := ⟨quadraticConjugationAlgEquiv D (x : rationalQuadraticAlgebra D),
    IsIntegral.map (quadraticConjugationAlgEquiv D) x.2⟩
  left_inv x := by
    apply Subtype.ext
    change star (star (x : rationalQuadraticAlgebra D)) = x
    simp
  right_inv x := by
    apply Subtype.ext
    change star (star (x : rationalQuadraticAlgebra D)) = x
    simp
  map_mul' x y := by
    apply Subtype.ext
    change star ((x : rationalQuadraticAlgebra D) *
      (y : rationalQuadraticAlgebra D)) =
        star (x : rationalQuadraticAlgebra D) * star (y : rationalQuadraticAlgebra D)
    simp
  map_add' x y := by
    apply Subtype.ext
    exact star_add (x : rationalQuadraticAlgebra D) (y : rationalQuadraticAlgebra D)

private theorem conjugation_formIdealGenerator (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ringOfIntegersQuadraticConjugation D (formIdealGenerator D Q hQ) =
      -(Q.b : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) -
        formIdealGenerator D Q hQ := by
  apply Subtype.ext
  change star ((formIdealGenerator D Q hQ :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) =
    -(Q.b : rationalQuadraticAlgebra D) -
      ((formIdealGenerator D Q hQ :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
          rationalQuadraticAlgebra D)
  rw [coe_formIdealGenerator]
  have htwo : (2 : rationalQuadraticAlgebra D) ≠ 0 := by norm_num
  apply mul_left_cancel₀ htwo
  calc
    (2 : rationalQuadraticAlgebra D) *
        star ((-(Q.b : rationalQuadraticAlgebra D) + QuadraticAlgebra.omega) / 2) =
        star ((2 : rationalQuadraticAlgebra D) *
        ((-(Q.b : rationalQuadraticAlgebra D) + QuadraticAlgebra.omega) / 2)) := by simp
    _ = star (-(Q.b : rationalQuadraticAlgebra D) + QuadraticAlgebra.omega) := by
      rw [mul_div_cancel₀ _ htwo]
    _ = -(Q.b : rationalQuadraticAlgebra D) - QuadraticAlgebra.omega := by
      ext <;> simp [QuadraticAlgebra.omega]
    _ = (2 : rationalQuadraticAlgebra D) *
        (-(Q.b : rationalQuadraticAlgebra D) -
          ((-(Q.b : rationalQuadraticAlgebra D) + QuadraticAlgebra.omega) / 2)) := by
      rw [mul_sub, mul_neg, mul_div_cancel₀ _ htwo]
      ring

private theorem formIdealGenerator_mul_conjugation (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formIdealGenerator D Q hQ *
        ringOfIntegersQuadraticConjugation D (formIdealGenerator D Q hQ) =
      (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) * Q.c := by
  rw [conjugation_formIdealGenerator]
  apply Subtype.ext
  change ((formIdealGenerator D Q hQ :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) *
      (-(Q.b : rationalQuadraticAlgebra D) - formIdealGenerator D Q hQ) =
    (Q.a : rationalQuadraticAlgebra D) * Q.c
  rw [coe_formIdealGenerator]
  have hω := rationalQuadraticAlgebra_omega_sq D
  have hdisc := congrArg (algebraMap ℤ (rationalQuadraticAlgebra D)) hQ
  simp only [discriminant, map_sub, map_pow, map_mul, map_ofNat] at hdisc
  simp only [← Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap] at hdisc ⊢
  calc
    _ = ((Q.b : rationalQuadraticAlgebra D) ^ 2 -
        QuadraticAlgebra.omega * QuadraticAlgebra.omega) / 4 := by ring
    _ = (Q.a : rationalQuadraticAlgebra D) * Q.c := by
      rw [hω, ← hdisc]
      ring

private theorem primitive_bezout (Q : IntegralBinaryQuadraticForm) (hprim : Q.Primitive) :
    ∃ x y z : ℤ, Q.a * x + Q.b * y + Q.c * z = 1 := by
  let g : ℤ := Q.a.gcd Q.b
  have hg : g ∣ Q.a := Int.gcd_dvd_left _ _
  have hg' : g ∣ Q.b := Int.gcd_dvd_right _ _
  have hunit : IsUnit ((g.gcd Q.c : ℕ) : ℤ) :=
    hprim _ ((Int.gcd_dvd_left _ _).trans hg)
      ((Int.gcd_dvd_left _ _).trans hg') (Int.gcd_dvd_right _ _)
  have hone : (g.gcd Q.c : ℤ) = 1 := by
    have := Int.isUnit_iff_natAbs_eq.mp hunit
    simpa using this
  refine ⟨Q.a.gcdA Q.b * g.gcdA Q.c, Q.a.gcdB Q.b * g.gcdA Q.c,
    g.gcdB Q.c, ?_⟩
  calc
    _ = g * g.gcdA Q.c + Q.c * g.gcdB Q.c := by
      dsimp [g]
      rw [Int.gcd_eq_gcd_ab Q.a Q.b]
      ring
    _ = (g.gcd Q.c : ℤ) := (Int.gcd_eq_gcd_ab _ _).symm
    _ = 1 := hone

/-- Quadratic conjugation preserves absolute ideal norm by identifying the
quotient rings. -/
theorem absNorm_map_quadraticConjugation (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) :
    Ideal.absNorm (I.map (ringOfIntegersQuadraticConjugation D)) = Ideal.absNorm I := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map (ringOfIntegersQuadraticConjugation D))
      (ringOfIntegersQuadraticConjugation D) rfl).symm.toEquiv

/-- A primitive form ideal times its quadratic conjugate is the principal
ideal generated by the leading coefficient. -/
theorem formAssociatedIdeal_mul_conjugation (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (hprim : Q.Primitive) :
    formAssociatedIdeal D Q hQ *
        (formAssociatedIdeal D Q hQ).map (ringOfIntegersQuadraticConjugation D) =
      Ideal.span {(Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))} := by
  let R := NumberField.RingOfIntegers (rationalQuadraticAlgebra D)
  let a : R := Q.a
  let b : R := Q.b
  let c : R := Q.c
  let θ : R := formIdealGenerator D Q hQ
  let θ' : R := ringOfIntegersQuadraticConjugation D θ
  have htrace : θ + θ' = -b := by
    dsimp [θ', θ, b]
    rw [conjugation_formIdealGenerator]
    ring
  have hnorm : θ * θ' = a * c := formIdealGenerator_mul_conjugation D Q hQ
  have hmap : (formAssociatedIdeal D Q hQ).map (ringOfIntegersQuadraticConjugation D) =
      Ideal.span {a, θ'} := by
    rw [formAssociatedIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    simp [a, θ', θ]
    rfl
  rw [hmap]
  change Ideal.span {a, θ} * Ideal.span {a, θ'} = Ideal.span {a}
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_right a a)
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_right a θ')
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_left a θ)
    · rw [hnorm]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right a c)
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    let J : Ideal R := Ideal.span {a * a, a * θ', θ * a, θ * θ'}
    have haa : a * a ∈ J := Ideal.subset_span (by simp)
    have hat : a * θ' ∈ J := Ideal.subset_span (by simp)
    have hta : θ * a ∈ J := Ideal.subset_span (by simp)
    have hac : a * c ∈ J := hnorm ▸ Ideal.subset_span (by simp)
    have hab : a * b ∈ J := by
      have heq : a * b = -(a * θ' + θ * a) := by
        linear_combination a * htrace
      rw [heq]
      exact J.neg_mem (J.add_mem hat hta)
    obtain ⟨x, y, z, hxyz⟩ := primitive_bezout Q hprim
    have hcast : a * (x : R) + b * (y : R) + c * (z : R) = 1 := by
      dsimp [a, b, c]
      simpa only [map_add, map_mul, map_one, Int.coe_castRingHom] using
        congrArg (Int.castRingHom R) hxyz
    have hsum := J.add_mem (J.add_mem (J.mul_mem_left (x : R) haa)
      (J.mul_mem_left (y : R) hab)) (J.mul_mem_left (z : R) hac)
    have heq : (x : R) * (a * a) + (y : R) * (a * b) + (z : R) * (a * c) = a := by
      linear_combination a * hcast
    change a ∈ J
    rwa [heq] at hsum

/-- The actual maximal-order ideal attached to a primitive form has absolute
norm equal to the absolute value of its leading coefficient. -/
theorem absNorm_formAssociatedIdeal_eq_natAbs (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (hprim : Q.Primitive) :
    Ideal.absNorm (formAssociatedIdeal D Q hQ) = Q.a.natAbs := by
  have hprod := congrArg Ideal.absNorm (formAssociatedIdeal_mul_conjugation D Q hQ hprim)
  rw [map_mul, absNorm_map_quadraticConjugation, Ideal.absNorm_span_singleton] at hprod
  have hrank : Module.finrank ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = 2 := by
    rw [NumberField.RingOfIntegers.rank]
    exact rationalQuadraticAlgebra_finrank_eq_two D
  rw [show (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
    algebraMap ℤ (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) Q.a by rfl,
    Algebra.norm_algebraMap, hrank, Int.natAbs_pow] at hprod
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) (by simpa [pow_two] using hprod)

end
end IntegralBinaryQuadraticForm
end PellPaper
