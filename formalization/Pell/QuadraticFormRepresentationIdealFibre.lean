import Pell.QuadraticFormRepresentationIdeal
import Pell.SquarefreeQuadraticIdealNormDivisorBound

/-!
# Partitioning primitive form representations by quotient ideals

For a fixed primitive quadratic form of discriminant `w*s^2`, this file maps
any finite family of representations of a nonzero integer `m` to the integral
quotient ideals constructed in `QuadraticFormRepresentationIdeal`.
Every image ideal has norm `|m|`, so the squarefree-kernel ideal count bounds
the number of image ideals by `tau(|m|)`.  The source family is also recorded
as the exact sum of its quotient-ideal fibres.

This is the finite bookkeeping in the manuscript.  Bounding the size
of one fibre by a fundamental-unit height argument remains separate.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

open NumberField

noncomputable section

local instance rationalQuadraticAlgebra_representationIdealFibre_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The finite image of a representation family under its quotient-ideal
assignment. -/
noncomputable def formRepresentationQuotientIdealImage
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (S : Finset (ℤ × ℤ)) :
    Finset (Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) :=
  S.image fun z => formRepresentationQuotientIdeal D Q hQ z.1 z.2

/-- A quotient ideal in the image of representations of `m` has norm
`|m|`. -/
theorem absNorm_eq_natAbs_of_mem_formRepresentationQuotientIdealImage
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (hprim : Q.Primitive) (ha : Q.a ≠ 0) (m : ℤ)
    (S : Finset (ℤ × ℤ))
    (hrep : ∀ z ∈ S, Q.eval z.1 z.2 = m)
    {J : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))}
    (hJ : J ∈ formRepresentationQuotientIdealImage D Q hQ S) :
    Ideal.absNorm J = m.natAbs := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hJ
  exact absNorm_formRepresentationQuotientIdeal_eq_natAbs
    D Q hQ hprim ha z.1 z.2 m (hrep z hz)

/-- For discriminant `w*s^2`, the quotient-ideal image of any finite family
of representations of nonzero `m` has cardinality at most `tau(|m|)`. -/
theorem card_formRepresentationQuotientIdealImage_le_card_divisors
    (w s : ℕ) (hw : Squarefree w) (hwone : 1 < w) (hs : 0 < s)
    (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((w * s ^ 2 : ℕ) : ℤ))]
    (hprim : Q.Primitive) (ha : Q.a ≠ 0) (m : ℤ) (hm : m ≠ 0)
    (S : Finset (ℤ × ℤ))
    (hrep : ∀ z ∈ S, Q.eval z.1 z.2 = m) :
    (formRepresentationQuotientIdealImage
      ((w * s ^ 2 : ℕ) : ℤ) Q hQ S).card ≤ m.natAbs.divisors.card := by
  classical
  let image := formRepresentationQuotientIdealImage
    ((w * s ^ 2 : ℕ) : ℤ) Q hQ S
  let target := {J : Ideal (NumberField.RingOfIntegers
    (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) //
      Ideal.absNorm J = m.natAbs}
  let f : {J // J ∈ image} → target := fun J =>
    ⟨J.1, absNorm_eq_natAbs_of_mem_formRepresentationQuotientIdealImage
      ((w * s ^ 2 : ℕ) : ℤ) Q hQ hprim ha m S hrep J.2⟩
  have hf : Function.Injective f := by
    intro J K hJK
    apply Subtype.ext
    simpa only [f] using congrArg (fun T : target => T.1) hJK
  let hfinite : Finite target :=
    Fintype.finite
      (Ideal.finite_setOfPred_absNorm_eq
        (S := NumberField.RingOfIntegers
          (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) m.natAbs).fintype
  have hcard : Nat.card {J // J ∈ image} ≤ Nat.card target :=
    @Nat.card_le_card_of_injective _ _ hfinite f hf
  have hsubtypeCard : Nat.card {J // J ∈ image} = image.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe image
  have himage : image.card ≤ Nat.card target := by
    rw [← hsubtypeCard]
    exact hcard
  have htarget : Nat.card target ≤ m.natAbs.divisors.card := by
    simpa only [target] using
      (squarefree_mul_sq_card_idealNormFibre_le_card_divisors
        w s m.natAbs hw hwone hs (Int.natAbs_ne_zero.mpr hm))
  exact himage.trans htarget

/-- Exact partition of a finite representation family by its assigned
quotient ideal. -/
theorem card_eq_sum_card_formRepresentationQuotientIdeal_fibres
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (S : Finset (ℤ × ℤ)) :
    S.card = ∑ J ∈ formRepresentationQuotientIdealImage D Q hQ S,
      (S.filter fun z => formRepresentationQuotientIdeal D Q hQ z.1 z.2 = J).card := by
  let f : ℤ × ℤ → Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
    fun z => formRepresentationQuotientIdeal D Q hQ z.1 z.2
  change S.card = ∑ J ∈ S.image f, (S.filter fun z => f z = J).card
  exact Finset.card_eq_sum_card_image f S

end
end IntegralBinaryQuadraticForm
end PellPaper
