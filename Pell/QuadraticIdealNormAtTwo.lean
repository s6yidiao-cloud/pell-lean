import Pell.QuadraticFormIdealNormEquality
import Mathlib.Data.ZMod.Basic

/-!
# Ideals of norm two at odd fundamental discriminants

For an odd positive fundamental discriminant `D`, an actual ideal of norm
two exists precisely when `D % 8 = 1`.  A norm-two ideal has quotient ring
`ZMod 2`; reducing the integral element `(-1 + sqrt(D))/2`, whose square
plus itself is `D/4`, forces `D/4` to be even.  Conversely, when `D % 8 = 1`,
the primitive form `[2, 1, -D/8]` has discriminant `D`, and its attached
maximal-order ideal has norm two.

The divisions `D/4` and `D/8` here are natural-number divisions; their exact
remainders are supplied by `D % 4 = 1` and `D % 8 = 1`, respectively.
No character-value identification is asserted.
-/

namespace PellPaper

open NumberField IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_atTwo_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private def idealQuotientEquivZModOfAbsNormEqPrime
    (K : Type*) [Field K] [NumberField K] (I : Ideal (𝓞 K))
    (p : ℕ) (hp : Nat.Prime p) (hI : Ideal.absNorm I = p) :
    (𝓞 K ⧸ I) ≃+* ZMod p := by
  have hcard : Nat.card (𝓞 K ⧸ I) = p := by
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hI
  let _ : Finite (𝓞 K ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite (𝓞 K ⧸ I)
  have hcard' : Fintype.card (𝓞 K ⧸ I) = p := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact (ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp hcard').symm

private theorem principalFormGenerator_sq_add
    (D : ℕ) (hmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    let θ := formIdealGenerator (D : ℤ) (principalFormOneModFour D)
      (discriminant_principalFormOneModFour D hmod)
    θ ^ 2 + θ = ((D / 4 : ℕ) : 𝓞 (rationalQuadraticAlgebra (D : ℤ))) := by
  dsimp only
  apply Subtype.ext
  change
    ((-((algebraMap ℤ (rationalQuadraticAlgebra (D : ℤ)))
        (principalFormOneModFour D).b) + QuadraticAlgebra.omega) / 2) ^ 2 +
      (-((algebraMap ℤ (rationalQuadraticAlgebra (D : ℤ)))
        (principalFormOneModFour D).b) + QuadraticAlgebra.omega) / 2 =
      ((D / 4 : ℕ) : rationalQuadraticAlgebra (D : ℤ))
  simp only [principalFormOneModFour, map_one]
  have hsplit : D = 4 * (D / 4) + 1 := by omega
  have hDfield : (D : rationalQuadraticAlgebra (D : ℤ)) =
      4 * ((D / 4 : ℕ) : rationalQuadraticAlgebra (D : ℤ)) + 1 := by
    exact_mod_cast hsplit
  have hω : (QuadraticAlgebra.omega : rationalQuadraticAlgebra (D : ℤ)) ^ 2 =
      (D : rationalQuadraticAlgebra (D : ℤ)) := by
    simpa only [pow_two, Int.cast_natCast] using rationalQuadraticAlgebra_omega_sq (D : ℤ)
  calc
    _ = ((QuadraticAlgebra.omega : rationalQuadraticAlgebra (D : ℤ)) ^ 2 - 1) / 4 := by ring
    _ = ((D / 4 : ℕ) : rationalQuadraticAlgebra (D : ℤ)) := by
      rw [hω, hDfield]
      ring

/-- For an odd positive fundamental discriminant, there is an actual ideal
of absolute norm two if and only if the discriminant is one modulo eight. -/
theorem rationalQuadraticAlgebra_exists_ideal_absNorm_eq_two_iff_mod_eight_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) (hodd : Odd D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (∃ I : Ideal (𝓞 (rationalQuadraticAlgebra (D : ℤ))), Ideal.absNorm I = 2) ↔
      D % 8 = 1 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have hmod : D % 4 = 1 := by
    rcases hD.2 with h | ⟨d, hDd, _, _⟩
    · exact h.2
    · have hodd' := Nat.odd_iff.mp hodd
      omega
  constructor
  · rintro ⟨I, hI⟩
    let R := 𝓞 (rationalQuadraticAlgebra (D : ℤ))
    let e := idealQuotientEquivZModOfAbsNormEqPrime
      (rationalQuadraticAlgebra (D : ℤ)) I 2 Nat.prime_two hI
    let red : R →+* ZMod 2 := e.toRingHom.comp (Ideal.Quotient.mk I)
    let θ : R := formIdealGenerator (D : ℤ) (principalFormOneModFour D)
      (discriminant_principalFormOneModFour D hmod)
    have hθ : θ ^ 2 + θ = ((D / 4 : ℕ) : R) := principalFormGenerator_sq_add D hmod
    have hred : red θ ^ 2 + red θ = ((D / 4 : ℕ) : ZMod 2) := by
      calc
        red θ ^ 2 + red θ = red (θ ^ 2 + θ) := by rw [map_add, map_pow]
        _ = red ((D / 4 : ℕ) : R) := congrArg red hθ
        _ = ((D / 4 : ℕ) : ZMod 2) := map_natCast red (D / 4)
    have hchar : ∀ x : ZMod 2, x ^ 2 + x = 0 := by decide
    have hzero : ((D / 4 : ℕ) : ZMod 2) = 0 := by
      rw [← hred]
      exact hchar _
    have hdiv : 2 ∣ D / 4 := (ZMod.natCast_eq_zero_iff (D / 4) 2).mp hzero
    have hparity : (D / 4) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · intro hmod8
    let Q : IntegralBinaryQuadraticForm := ⟨2, 1, -((D / 8 : ℕ) : ℤ)⟩
    have hdisc : Q.discriminant = (D : ℤ) := by
      have hsplit : D = 8 * (D / 8) + 1 := by omega
      have hcast : (D : ℤ) = 8 * ((D / 8 : ℕ) : ℤ) + 1 := by exact_mod_cast hsplit
      change (1 : ℤ) ^ 2 - 4 * 2 * (-((D / 8 : ℕ) : ℤ)) = (D : ℤ)
      rw [hcast]
      ring
    have hprim : Q.Primitive := by
      intro z _ hzb _
      exact isUnit_of_dvd_one hzb
    refine ⟨formAssociatedIdeal (D : ℤ) Q hdisc, ?_⟩
    rw [absNorm_formAssociatedIdeal_eq_natAbs (D : ℤ) Q hdisc hprim]
    norm_num [Q]

end

end PellPaper
