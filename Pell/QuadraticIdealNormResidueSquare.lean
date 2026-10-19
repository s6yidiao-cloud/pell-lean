import Pell.QuadraticFormIdealNormEquality
import Pell.QuadraticIdealNormOddSplit
import Mathlib.Data.ZMod.Basic

/-!
# A residue square forced by an ideal of prime norm

For any nonsquare integer `D`, an ideal of absolute norm `p`, with `p` prime,
in the ring of integers of the rational quadratic algebra gives a square
root of `D` modulo `p`.  Its quotient ring has cardinality `p`, so its
canonical prime-ring map is a ring equivalence with `ZMod p`.  Reducing the
integral element `sqrt(D)` through this equivalence gives the square root.

This converse includes `p = 2` and primes dividing `D`; it does not need a
fundamental-discriminant hypothesis or a supplied quotient equivalence.
For odd primes away from a positive fundamental discriminant, composing it
with the primitive-form construction gives the corresponding equivalence.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_residueSquare_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- An ideal of prime absolute norm forces the defining radicand to be a
square modulo that prime.  The prime may be `2` or divide the radicand;
only the existing no-rational-root field condition is assumed on `D`. -/
theorem rationalQuadraticAlgebra_exists_sq_mod_of_ideal_absNorm_eq_prime
    (D : ℤ) (p : ℕ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (hp : Nat.Prime p)
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (hI : Ideal.absNorm I = p) :
    ∃ r : ℤ, r ^ 2 ≡ D [ZMOD (p : ℤ)] := by
  let R := NumberField.RingOfIntegers (rationalQuadraticAlgebra D)
  have hcard : Nat.card (R ⧸ I) = p := by
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hI
  let _ : Finite (R ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let _ : Fintype (R ⧸ I) := Fintype.ofFinite (R ⧸ I)
  have hcard' : Fintype.card (R ⧸ I) = p := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let e : (R ⧸ I) ≃+* ZMod p := (ZMod.ringEquivOfPrime (R ⧸ I) hp hcard').symm
  let red : R →+* ZMod p := e.toRingHom.comp (Ideal.Quotient.mk I)
  let ω : R := ⟨QuadraticAlgebra.omega, rationalQuadraticAlgebra_omega_isIntegral D⟩
  have hω : ω ^ 2 = (D : R) := by
    apply Subtype.ext
    change (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 =
      (D : rationalQuadraticAlgebra D)
    simpa only [pow_two] using rationalQuadraticAlgebra_omega_sq D
  have hred : red ω ^ 2 = (D : ZMod p) := by
    calc
      red ω ^ 2 = red (ω ^ 2) := (map_pow red ω 2).symm
      _ = red (D : R) := congrArg red hω
      _ = (D : ZMod p) := map_intCast red D
  obtain ⟨r, hr⟩ := ZMod.intCast_surjective (red ω)
  refine ⟨r, (ZMod.intCast_eq_intCast_iff (r ^ 2) D p).mp ?_⟩
  simpa only [Int.cast_pow, hr] using hred

/-- For an odd prime away from a positive fundamental discriminant, an
actual ideal of norm `p` exists if and only if the discriminant is a square
modulo `p`.  Both directions concern the actual ring of integers. -/
theorem rationalQuadraticAlgebra_exists_ideal_absNorm_eq_prime_iff_sq_mod
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      Ideal.absNorm I = p) ↔ ∃ r : ℤ, r ^ 2 ≡ (D : ℤ) [ZMOD (p : ℤ)] := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  constructor
  · rintro ⟨I, hI⟩
    exact rationalQuadraticAlgebra_exists_sq_mod_of_ideal_absNorm_eq_prime (D : ℤ) p hp I hI
  · intro hroot
    obtain ⟨P, _, _, hP⟩ :=
      rationalQuadraticAlgebra_exists_primeIdeal_absNorm_eq_prime_of_sq_mod
        D p hD hp hp2 hpD hroot
    exact ⟨P, hP⟩

end

end PellPaper
