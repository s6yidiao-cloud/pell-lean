import Pell.QuadraticFormIdealNormEquality
import Mathlib.RingTheory.Int.Basic

/-!
# A norm-prime ideal from a quadratic residue at an odd prime

If an odd prime `p` does not divide a positive fundamental discriminant `D`
and `D` is a square modulo `p`, an integer root can be adjusted to the parity
required by `D`.  The resulting primitive form `[p, b, (b²-D)/(4p)]`
has discriminant `D`.  The proved form-ideal norm equality therefore gives
an actual maximal ideal over `(p)` of absolute norm `p`.

This module does not identify the residue criterion with a character value,
construct the second split prime, or count ideals of higher prime-power norm.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_oddSplit_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem positiveFundamentalDiscriminant_eq_square_add_four_mul
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    ∃ u v : ℤ, (D : ℤ) = u ^ 2 + 4 * v := by
  rcases hD.2 with hodd | ⟨d, rfl, _, _⟩
  · refine ⟨1, (D / 4 : ℕ), ?_⟩
    have hsplit : D = 1 + 4 * (D / 4) := by omega
    exact_mod_cast hsplit
  · refine ⟨0, d, ?_⟩
    norm_num

private theorem exists_primitiveForm_leadingCoefficient_prime_of_sq_mod
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D)
    (hroot : ∃ r : ℤ, r ^ 2 ≡ (D : ℤ) [ZMOD (p : ℤ)]) :
    ∃ Q : IntegralBinaryQuadraticForm,
      Q.Primitive ∧ Q.discriminant = (D : ℤ) ∧ Q.a = (p : ℤ) := by
  obtain ⟨r, hr⟩ := hroot
  obtain ⟨u, v, hDrep⟩ := positiveFundamentalDiscriminant_eq_square_add_four_mul D hD
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hp.odd_of_ne_two hp2
  obtain ⟨t, hpt⟩ := hpodd
  let b : ℤ := r + (p : ℤ) * (u - r)
  have hbeq : b = u + 2 * t * (u - r) := by
    dsimp [b]
    rw [hpt]
    ring
  have hfour : (4 : ℤ) ∣ b ^ 2 - (D : ℤ) := by
    refine ⟨t * (u - r) * u + t ^ 2 * (u - r) ^ 2 - v, ?_⟩
    rw [hbeq, hDrep]
    ring
  have hbr : b ≡ r [ZMOD (p : ℤ)] := by
    dsimp [b]
    exact Int.add_modulus_mul_modEq_iff.mpr (Int.ModEq.refl r)
  have hpdiv : (p : ℤ) ∣ b ^ 2 - (D : ℤ) := by
    exact Int.modEq_iff_dvd.mp ((hbr.pow 2).trans hr).symm
  have hcoprime : (4 : ℕ).Coprime p := by
    have hpodd' := hp.odd_of_ne_two hp2
    simpa using hpodd'.coprime_two_left.pow_left 2
  have hfourp : (4 * (p : ℤ)) ∣ b ^ 2 - (D : ℤ) := by
    exact ((Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcoprime)).mul_dvd
      hfour hpdiv)
  obtain ⟨c, hc⟩ := hfourp
  let Q : IntegralBinaryQuadraticForm := ⟨p, b, c⟩
  have hdisc : Q.discriminant = (D : ℤ) := by
    dsimp [Q, IntegralBinaryQuadraticForm.discriminant]
    linear_combination hc
  have hpz : Prime (p : ℤ) := by
    exact Nat.prime_iff_prime_int.mp hp
  have hpb : ¬ (p : ℤ) ∣ b := by
    intro hpb
    have hpDint : (p : ℤ) ∣ (D : ℤ) := by
      have hsq : (p : ℤ) ∣ b ^ 2 := dvd_pow hpb (by decide)
      have h := dvd_sub hsq hpdiv
      simpa using h
    exact hpD (by exact_mod_cast hpDint)
  have hprim : Q.Primitive := by
    intro z hza hzb _
    have hab : IsCoprime (p : ℤ) b := hpz.coprime_iff_not_dvd.mpr hpb
    exact hab.isUnit_of_dvd' hza hzb
  exact ⟨Q, hprim, hdisc, rfl⟩

/-- A residue square at an odd prime away from the discriminant constructs
an actual maximal ideal of norm `p` over `(p)`, using the primitive form
whose leading coefficient is `p`. -/
theorem rationalQuadraticAlgebra_exists_primeIdeal_absNorm_eq_prime_of_sq_mod
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D)
    (hroot : ∃ r : ℤ, r ^ 2 ≡ (D : ℤ) [ZMOD (p : ℤ)]) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∃ P : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      P.IsMaximal ∧ P.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) ∧
        Ideal.absNorm P = p := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  obtain ⟨Q, hprim, hdisc, ha⟩ :=
    exists_primitiveForm_leadingCoefficient_prime_of_sq_mod D p hD hp hp2 hpD hroot
  let P := IntegralBinaryQuadraticForm.formAssociatedIdeal (D : ℤ) Q hdisc
  have hnorm : Ideal.absNorm P = p := by
    rw [IntegralBinaryQuadraticForm.absNorm_formAssociatedIdeal_eq_natAbs
      (D : ℤ) Q hdisc hprim, ha]
    simp
  have hPprime : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    ((Nat.irreducible_iff_nat_prime _).mpr (hnorm ▸ hp))
  have hPne : P ≠ ⊥ := by
    intro hP
    have h := hnorm
    rw [hP, Ideal.absNorm_bot] at h
    exact hp.ne_zero h.symm
  have hmax : P.IsMaximal := hPprime.isMaximal hPne
  have hunder : P.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    simpa [Ideal.under_def, hnorm] using
      (Ideal.span_singleton_absNorm (I := P) (hnorm ▸ hp)).symm
  exact ⟨P, hmax, hunder, hnorm⟩

end

end PellPaper
