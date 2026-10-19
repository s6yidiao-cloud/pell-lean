import Pell.QuadraticIdealNormFibreSurjectivity

/-!
# Euler-coefficient assembly with proved ideal-norm multiplicativity

The coprime ideal-norm fibre equivalence supplies the multiplicativity
previously left as an explicit interface in
`QuadraticIdealNormEulerCoefficient`.  Consequently the only remaining
arithmetic input in the theorems below is the local prime-power geometric
sum.  This module does not establish those local identities (or any
splitting, conductor, or analytic factorization result).
-/

namespace PellPaper

open NumberField

noncomputable section

/-- If the raw ideal-norm coefficient has the required geometric value at
every rational prime power, its zero-normalized arithmetic function equals
the Euler coefficient of `ζ * L(χ, ·)`.  Multiplicativity is supplied by the
proved coprime ideal-fibre factorization, not assumed by the caller. -/
theorem idealNormCoefficient_eq_zetaMul_of_primePowerGeometricSum
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
        ∑ j ∈ Finset.range (k + 1), χ p ^ j) :
    idealNormCoefficient K = χ.zetaMul := by
  exact idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum
    K χ (idealNormCoefficient_isMultiplicative K) hprimepow

/-- The prime-power check at exponent zero is automatic, so positive local
prime-power identities already assemble the full Euler coefficient. -/
theorem idealNormCoefficient_eq_zetaMul_of_primePowerGeometricSum_of_pos
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p → 0 < k →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
        ∑ j ∈ Finset.range (k + 1), χ p ^ j) :
    idealNormCoefficient K = χ.zetaMul := by
  exact
    idealNormCoefficient_eq_zetaMul_of_isMultiplicative_and_primePowerGeometricSum_of_pos
      K χ (idealNormCoefficient_isMultiplicative K) hprimepow

/-- The assembled zero-normalized identity recovers the raw ideal-norm
coefficient at every positive integer. -/
theorem raw_idealNormCoefficient_eq_zetaMul_of_primePowerGeometricSum_of_pos
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprimepow : ∀ p k : ℕ, Nat.Prime p → 0 < k →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
        ∑ j ∈ Finset.range (k + 1), χ p ^ j)
    {n : ℕ} (hn : n ≠ 0) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) = χ.zetaMul n := by
  rw [← idealNormCoefficient_apply_of_ne_zero K hn]
  exact congrArg (fun f : ArithmeticFunction ℂ => f n)
    (idealNormCoefficient_eq_zetaMul_of_primePowerGeometricSum_of_pos K χ hprimepow)

end

end PellPaper
