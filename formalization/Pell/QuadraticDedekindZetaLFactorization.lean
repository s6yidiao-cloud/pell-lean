import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# A conditional Dedekind-zeta/Dirichlet-`L` factorization

For a number field `K` and a complex Dirichlet character `χ`, this module
records the analytic implication of the exact coefficient identity
\[
  \#\{I \subseteq \mathcal O_K : N(I)=n\}=\sum_{d\mid n}\chi(d)
  \qquad(n>0).
\]
The right-hand side is represented by `χ.zetaMul n`.  The theorem below does
not establish that identity for a quadratic field, identify `χ` with a
Kronecker character, or prove primitivity.  Those are the separate arithmetic
frontier needed for the manuscript's class-number formula.
-/

namespace PellPaper

noncomputable section

open NumberField
open scoped LSeries.notation

set_option maxHeartbeats 1000000

/-- If the nonzero ideal-norm coefficients of the Dedekind zeta function are
the Dirichlet convolution of the constant-one sequence with `χ`, then in the
half-plane of absolute convergence the Dedekind zeta function factors as the
Riemann zeta function times the analytically continued Dirichlet `L`-function.

The coefficient hypothesis is the exact unproved arithmetic input in the
quadratic-field application.  The value at `n = 0` is deliberately absent:
`LSeries` ignores that coefficient. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction_of_idealNormCoefficient_eq_zetaMul
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) = χ.zetaMul n) :
    NumberField.dedekindZeta K s =
      riemannZeta s * DirichletCharacter.LFunction χ s := by
  rw [NumberField.dedekindZeta]
  calc
    LSeries (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s =
        LSeries (χ.zetaMul : ℕ → ℂ) s :=
      LSeries_congr (fun {n} hn ↦ hcoeff n hn) s
    _ = LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s *
        LSeries (toArithmeticFunction (χ ·) : ArithmeticFunction ℂ) s := by
      rw [DirichletCharacter.zetaMul]
      apply ArithmeticFunction.LSeries_mul'
      · exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
      · exact (LSeriesSummable_congr _ fun {n} hn ↦
          (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
            (χ.LSeriesSummable_of_one_lt_re hs)
    _ = riemannZeta s * LSeries (χ ·) s := by
      congr 1
      · exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
      · exact (LSeries_congr (fun {n} hn ↦
          χ.apply_eq_toArithmeticFunction_apply hn) s).symm
    _ = riemannZeta s * DirichletCharacter.LFunction χ s := by
      rw [χ.LFunction_eq_LSeries hs]

end

end PellPaper
