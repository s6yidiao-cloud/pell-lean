import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Euler-product coefficient reductions for quadratic ideal norms

This module makes the prime-power frontier in the conditional
Dedekind-zeta/Dirichlet-`L` factorization explicit.  It does **not** prove
that the number of ideals of a fixed norm is multiplicative, and it does not
identify the local ideal-norm coefficients in a quadratic field.  Instead it
proves the exact assembly statement: once those two arithmetic inputs are
available, checking every prime power is sufficient for the nonzero
coefficient identity used by the analytic factorization.

The raw norm-zero fibre has cardinality one, whereas an `ArithmeticFunction`
must vanish at zero.  Accordingly `idealNormCoefficient` is deliberately
zero-normalized at `0`; every bridge back to the raw coefficient retains an
explicit nonzero hypothesis.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- The zero-normalized ideal-norm coefficient function.  At each positive
integer it is the number of integral ideals of that absolute norm. -/
noncomputable def idealNormCoefficient (K : Type*) [Field K] [NumberField K] :
    ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ), by simp⟩

@[simp]
theorem idealNormCoefficient_zero (K : Type*) [Field K] [NumberField K] :
    idealNormCoefficient K 0 = 0 := by
  simp [idealNormCoefficient]

/-- Away from zero, the zero-normalized arithmetic function is the raw
Dedekind-zeta coefficient. -/
theorem idealNormCoefficient_apply_of_ne_zero
    (K : Type*) [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealNormCoefficient K n =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
  simp [idealNormCoefficient, hn]

/-- There is exactly one integral ideal of absolute norm one, namely the unit
ideal. -/
theorem raw_idealNormCoefficient_one
    (K : Type*) [Field K] [NumberField K] :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} : ℂ) = 1 := by
  have hcard : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · constructor
      rintro ⟨I, hI⟩ ⟨J, hJ⟩
      apply Subtype.ext
      exact (Ideal.absNorm_eq_one_iff.mp hI).trans
        (Ideal.absNorm_eq_one_iff.mp hJ).symm
    · exact ⟨⟨⊤, Ideal.absNorm_top⟩⟩
  exact_mod_cast hcard

/-- The zero-normalized coefficient also has the expected value at one. -/
theorem idealNormCoefficient_one
    (K : Type*) [Field K] [NumberField K] :
    idealNormCoefficient K 1 = 1 := by
  rw [idealNormCoefficient_apply_of_ne_zero K one_ne_zero]
  exact raw_idealNormCoefficient_one K

/-- The local Euler coefficient of `ζ * L(χ, \cdot)` at a rational prime
power is the finite geometric sum of the character values. -/
theorem zetaMul_apply_prime_pow
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {p k : ℕ}
    (hp : Nat.Prime p) :
    χ.zetaMul (p ^ k) = ∑ j ∈ Finset.range (k + 1), χ p ^ j := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp [toArithmeticFunction, hp.ne_zero]

/-- Prime-power agreement, together with the explicitly retained
multiplicativity of the ideal-norm coefficient, gives the full equality of
zero-normalized arithmetic functions. -/
theorem idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_eq_on_primePowers
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hmult : (idealNormCoefficient K).IsMultiplicative)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p →
      idealNormCoefficient K (p ^ k) = χ.zetaMul (p ^ k)) :
    idealNormCoefficient K = χ.zetaMul := by
  exact (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (idealNormCoefficient K) hmult χ.zetaMul χ.isMultiplicative_zetaMul).mpr hprimepow

/-- The same Euler-product assembly written directly with raw positive
ideal-norm coefficients and the explicit geometric local factor. -/
theorem idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hmult : (idealNormCoefficient K).IsMultiplicative)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
        ∑ j ∈ Finset.range (k + 1), χ p ^ j) :
    idealNormCoefficient K = χ.zetaMul := by
  apply idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_eq_on_primePowers K χ hmult
  intro p k hp
  rw [idealNormCoefficient_apply_of_ne_zero K (pow_ne_zero _ hp.ne_zero)]
  rw [zetaMul_apply_prime_pow χ hp]
  exact hprimepow p k hp

/-- The `k = 0` prime-power check is automatic: only positive local
prime-power identities need be supplied to assemble the Euler coefficients. -/
theorem idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum_of_pos
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hmult : (idealNormCoefficient K).IsMultiplicative)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p → 0 < k →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
        ∑ j ∈ Finset.range (k + 1), χ p ^ j) :
    idealNormCoefficient K = χ.zetaMul := by
  apply idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum K χ hmult
  intro p k hp
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact hprimepow p k hp (Nat.pos_of_ne_zero hk)

/-- The zero-normalized Euler-product identity recovers the raw coefficient
identity at every positive norm. -/
theorem raw_idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hmult : (idealNormCoefficient K).IsMultiplicative)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
        ∑ j ∈ Finset.range (k + 1), χ p ^ j)
    {n : ℕ} (hn : n ≠ 0) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) = χ.zetaMul n := by
  rw [← idealNormCoefficient_apply_of_ne_zero K hn]
  exact congrArg (fun f : ArithmeticFunction ℂ => f n)
    (idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum
      K χ hmult hprimepow)

end

end PellPaper
