import Pell.QuadraticDedekindZetaLFactorization

/-!
# A conditional residue bridge for the quadratic zeta factorization

This file separates the analytic passage from a right-half-plane identity
`ζ_K(s) = ζ(s) L(s, χ)` to the equality of residues at `s = 1`.  The
right-hand limit of the Dirichlet `L`-function is retained as an explicit
hypothesis.  In particular, this file does not assert that the character is
nontrivial or primitive, and does not infer regularity of its `L`-function at
one.
-/

namespace PellPaper

noncomputable section

open Filter Topology NumberField
open scoped LSeries.notation

/-- The Riemann-zeta residue theorem, restricted to the real approach from
the right. -/
theorem tendsto_sub_one_mul_riemannZeta_ofReal_nhdsGT :
    Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] 1) (𝓝 1) := by
  have hcoe : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    exact Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun s hs ↦ by
        simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
        exact_mod_cast ne_of_gt hs)
  change Tendsto
    ((fun z : ℂ ↦ (z - 1) * riemannZeta z) ∘ fun s : ℝ ↦ (s : ℂ))
    (𝓝[>] 1) (𝓝 1)
  exact riemannZeta_residue_one.comp hcoe

/-- A right-half-plane factorization gives the expected residue equality once
the `L`-function has the displayed right-hand limit at one.  This statement is
deliberately conditional: it supplies neither continuity nor nontriviality of
the character. -/
theorem dedekindZeta_residue_eq_LFunction_apply_one_of_rightHalfPlaneFactorization
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hfactor : ∀ s : ℝ, 1 < s →
      NumberField.dedekindZeta K (s : ℂ) =
        riemannZeta (s : ℂ) * DirichletCharacter.LFunction χ (s : ℂ))
    (hL : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1))) :
    (NumberField.dedekindZeta_residue K : ℂ) =
      DirichletCharacter.LFunction χ 1 := by
  have hdedekind : Tendsto
      (fun s : ℝ ↦ ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (𝓝[>] 1) (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
    simpa using NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hproduct : Tendsto
      (fun s : ℝ ↦
        (((s : ℂ) - 1) * riemannZeta (s : ℂ)) *
          DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1)) := by
    simpa using tendsto_sub_one_mul_riemannZeta_ofReal_nhdsGT.mul hL
  have hfactorLimit : Tendsto
      (fun s : ℝ ↦ ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1)) := by
    refine hproduct.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hfactor s hs]
    ring
  exact tendsto_nhds_unique hdedekind hfactorLimit

/-- The exact ideal-norm coefficient identity from the factorization module,
together with the explicit right-hand `L`-limit at one, yields
`Res ζ_K = L(1, χ)`.  The coefficient identity remains a separate arithmetic
input; no quadratic-character identification or primitivity is used here. -/
theorem dedekindZeta_residue_eq_LFunction_apply_one_of_idealNormCoefficient_eq_zetaMul
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) = χ.zetaMul n)
    (hL : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1))) :
    (NumberField.dedekindZeta_residue K : ℂ) =
      DirichletCharacter.LFunction χ 1 := by
  apply dedekindZeta_residue_eq_LFunction_apply_one_of_rightHalfPlaneFactorization K χ
    (hL := hL)
  intro s hs
  exact dedekindZeta_eq_riemannZeta_mul_LFunction_of_idealNormCoefficient_eq_zetaMul
    K χ (by simpa using hs) hcoeff

end

end PellPaper
