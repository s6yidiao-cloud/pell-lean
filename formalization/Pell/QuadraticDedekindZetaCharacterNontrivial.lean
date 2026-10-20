import Pell.QuadraticDedekindZetaResidueBridge

/-!
# Nontriviality forced by a Dedekind-zeta factorization

A real right-half-plane identity `ζ_K = ζ L(χ)` for an actual number field
forces `χ` to be nontrivial: the left side has a finite simple-pole residue,
while the trivial-character right side would have a nonzero double-pole
coefficient.  The resulting holomorphy of `L(χ)` supplies its right limit
at one.  No quadraticity, primitivity, conductor identity, or assumed
regularity of the L-function is used.
-/

namespace PellPaper

noncomputable section

open Filter Topology NumberField

/-- An actual number-field factorization on the real interval `s > 1`
cannot involve the trivial Dirichlet character. -/
theorem dirichletCharacter_ne_one_of_dedekindZeta_rightHalfPlaneFactorization
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hfactor : ∀ s : ℝ, 1 < s →
      NumberField.dedekindZeta K (s : ℂ) =
        riemannZeta (s : ℂ) * DirichletCharacter.LFunction χ (s : ℂ)) :
    χ ≠ 1 := by
  intro hχ
  subst χ
  have hcoe : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    exact Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun s hs ↦ by
        simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
        exact_mod_cast ne_of_gt hs)
  have hlinear : Tendsto (fun s : ℝ ↦ (s : ℂ) - 1) (𝓝[>] 1) (𝓝 0) := by
    simpa using (hcoe.mono_right nhdsWithin_le_nhds).sub_const (1 : ℂ)
  have hdedekind : Tendsto
      (fun s : ℝ ↦ ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (𝓝[>] 1) (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
    simpa using NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hzero : Tendsto
      (fun s : ℝ ↦ ((s : ℂ) - 1) ^ 2 * NumberField.dedekindZeta K (s : ℂ))
      (𝓝[>] 1) (𝓝 0) := by
    simpa only [zero_mul, pow_two, mul_assoc] using hlinear.mul hdedekind
  have htrivial : Tendsto
      (fun s : ℝ ↦ ((s : ℂ) - 1) * DirichletCharacter.LFunctionTrivChar N (s : ℂ))
      (𝓝[>] 1) (𝓝 (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹))) :=
    DirichletCharacter.LFunctionTrivChar_residue_one.comp hcoe
  have hproduct := tendsto_sub_one_mul_riemannZeta_ofReal_nhdsGT.mul htrivial
  have hnonzero : Tendsto
      (fun s : ℝ ↦ ((s : ℂ) - 1) ^ 2 * NumberField.dedekindZeta K (s : ℂ))
      (𝓝[>] 1) (𝓝 (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹))) := by
    simp only [one_mul] at hproduct
    refine hproduct.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hfactor s hs]
    ring
  have hresidue : (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) ≠ 0 := by
    simpa only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self] using
      DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N
  exact hresidue (tendsto_nhds_unique hnonzero hzero)

/-- The same actual right-half-plane factorization supplies the right-hand
limit of `L(χ)` at one, without a separate L-function regularity premise. -/
theorem tendsto_LFunction_ofReal_nhdsGT_one_of_dedekindZeta_rightHalfPlaneFactorization
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hfactor : ∀ s : ℝ, 1 < s →
      NumberField.dedekindZeta K (s : ℂ) =
        riemannZeta (s : ℂ) * DirichletCharacter.LFunction χ (s : ℂ)) :
    Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  have hχ := dirichletCharacter_ne_one_of_dedekindZeta_rightHalfPlaneFactorization K χ hfactor
  have hcontinuous := (DirichletCharacter.differentiable_LFunction hχ).continuous
  simpa only [Function.comp_def, Complex.ofReal_one] using
    ((hcontinuous.comp Complex.continuous_ofReal).tendsto (1 : ℝ)).mono_left
      nhdsWithin_le_nhds

end

end PellPaper
