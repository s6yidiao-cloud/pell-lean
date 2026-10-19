import Mathlib.Analysis.Fourier.ZMod

/-!
# Primitive Dirichlet Gauss sums at arbitrary nonzero level

The standard Gauss sum of a primitive complex Dirichlet character has norm
the square root of its level. The level may be composite. The proof uses
the primitive-character Fourier formula and discrete Fourier inversion,
not the finite-field Gauss-sum cardinality theorem.
-/

namespace PellPaper

noncomputable section

open scoped ZMod

/-- Fourier inversion computes the squared norm of the standard Gauss sum
of a primitive character at any nonzero level, including composite levels. -/
theorem primitiveDirichletCharacter_gaussSum_normSq
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ ZMod.stdAddChar) = (N : ℝ) := by
  have hfourier : ZMod.dft (χ : ZMod N → ℂ) =
      fun k ↦ χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hinversion := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [hfourier, ZMod.dft_mul_const, ZMod.dft_comp_neg] at hinversion
  have hconj : ZMod.dft ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) 1 =
      star (gaussSum χ ZMod.stdAddChar) := by
    rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift,
      star_gaussSum_eq, AddChar.inv_mulShift]
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at hinversion
  rw [hconj] at hinversion
  change (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) *
    gaussSum χ ZMod.stdAddChar = (N : ℂ) at hinversion
  rw [← Complex.normSq_eq_conj_mul_self] at hinversion
  exact_mod_cast hinversion

/-- The standard primitive Gauss-sum norm formula needs no primality
assumption on the level and no nonprincipal hypothesis. -/
theorem primitiveDirichletCharacter_gaussSum_norm
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (N : ℝ) := by
  rw [Complex.norm_def, primitiveDirichletCharacter_gaussSum_normSq χ hχ]

end
end PellPaper
