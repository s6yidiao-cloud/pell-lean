import Pell.QuadraticOrderPellPowerDescent
import Pell.QuadraticOrderPellRationalDenominator
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

/-!
# Trace, norm, and half-integral coordinates in a quadratic algebra

For the rational quadratic algebra with `ω² = d`, this module computes the
field trace and norm in its displayed two-coordinate basis.  Applied to an
element of the ring of integers, the standard integrality theorems for trace
and norm give integral values for
`2 * re x` and `re x² - d * im x²`.

When `d` is the cast of a squarefree natural number, the squarefree rational
denominator lemma upgrades these two facts to half-integrality of both
coordinates.  Through `QuadraticOrderPellPowerDescent`, this proves the
elementwise containment `2 * 𝓞_K ⊆ ℤ[√d]` in that squarefree branch.
-/

namespace PellPaper

private theorem rationalQuadraticAlgebra_basis_zero (d : ℤ) :
    (QuadraticAlgebra.basis (d : ℚ) 0 :
      Fin 2 → rationalQuadraticAlgebra d) 0 = 1 := by
  simp [QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun,
    QuadraticAlgebra.linearEquivTuple_symm_apply]
  ext <;> rfl

private theorem rationalQuadraticAlgebra_basis_one (d : ℤ) :
    (QuadraticAlgebra.basis (d : ℚ) 0 :
      Fin 2 → rationalQuadraticAlgebra d) 1 = QuadraticAlgebra.omega := by
  simp [QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun,
    QuadraticAlgebra.linearEquivTuple_symm_apply]
  ext <;> rfl

/-- The left-multiplication matrix in the coordinate basis `1, ω`, where
`ω² = d`. -/
theorem rationalQuadraticAlgebra_leftMulMatrix (d : ℤ)
    (x : rationalQuadraticAlgebra d) :
    Algebra.leftMulMatrix (QuadraticAlgebra.basis (d : ℚ) 0) x =
      !![x.re, (d : ℚ) * x.im; x.im, x.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply,
    Matrix.of_apply]
  fin_cases j
  · simp only [Fin.zero_eta]
    rw [rationalQuadraticAlgebra_basis_zero]
    fin_cases i
    · change (x * 1).re = x.re
      simp
    · change (x * 1).im = x.im
      simp
  · change ![(x * (QuadraticAlgebra.basis (d : ℚ) 0) 1).re,
      (x * (QuadraticAlgebra.basis (d : ℚ) 0) 1).im] i =
        !![x.re, (d : ℚ) * x.im; x.im, x.re] i 1
    rw [rationalQuadraticAlgebra_basis_one]
    fin_cases i
    · change (x * QuadraticAlgebra.omega).re = (d : ℚ) * x.im
      simp [QuadraticAlgebra.omega]
    · change (x * QuadraticAlgebra.omega).im = x.re
      simp [QuadraticAlgebra.omega]

/-- The algebra trace is twice the scalar coordinate in the rational
quadratic algebra. -/
theorem rationalQuadraticAlgebra_trace_apply (d : ℤ)
    (x : rationalQuadraticAlgebra d) :
    (Algebra.trace ℚ (rationalQuadraticAlgebra d)) x = 2 * x.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0),
    rationalQuadraticAlgebra_leftMulMatrix, Matrix.trace_fin_two]
  exact (two_mul _).symm

/-- The algebra norm is the usual quadratic expression in the two rational
coordinates. -/
theorem rationalQuadraticAlgebra_norm_apply (d : ℤ)
    (x : rationalQuadraticAlgebra d) :
    (Algebra.norm ℚ) x = x.re * x.re - (d : ℚ) * x.im * x.im := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (d : ℚ) 0),
    rationalQuadraticAlgebra_leftMulMatrix, Matrix.det_fin_two]
  simp

/-- An algebraic integer in the rational quadratic algebra has half-integral
scalar coordinate. -/
theorem rationalQuadraticAlgebra_exists_int_two_mul_re
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
    ∃ t : ℤ, (t : ℚ) = 2 * (x : rationalQuadraticAlgebra d).re := by
  have hxint : IsIntegral ℤ (x : rationalQuadraticAlgebra d) := by
    exact (NumberField.RingOfIntegers.isIntegral x).algebraMap
  have htrace : IsIntegral ℤ
      ((Algebra.trace ℚ (rationalQuadraticAlgebra d))
        (x : rationalQuadraticAlgebra d)) :=
    Algebra.isIntegral_trace hxint
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrace
  refine ⟨t, ?_⟩
  exact ht.trans (rationalQuadraticAlgebra_trace_apply d
    (x : rationalQuadraticAlgebra d))

/-- The usual quadratic norm expression of an algebraic integer is an
integer. -/
theorem rationalQuadraticAlgebra_exists_int_norm
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
    ∃ n : ℤ, (n : ℚ) =
      (x : rationalQuadraticAlgebra d).re *
          (x : rationalQuadraticAlgebra d).re -
        (d : ℚ) * (x : rationalQuadraticAlgebra d).im *
          (x : rationalQuadraticAlgebra d).im := by
  have hxint : IsIntegral ℤ (x : rationalQuadraticAlgebra d) := by
    exact (NumberField.RingOfIntegers.isIntegral x).algebraMap
  have hnorm : IsIntegral ℤ
      ((Algebra.norm ℚ) (x : rationalQuadraticAlgebra d)) :=
    Algebra.isIntegral_norm ℚ hxint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm
  refine ⟨n, ?_⟩
  exact hn.trans (rationalQuadraticAlgebra_norm_apply d
    (x : rationalQuadraticAlgebra d))

/-- In the squarefree branch, every algebraic integer has half-integral
coordinates in the basis `1, √D`. -/
theorem quadraticOrderPellHalfIntegralCoordinates_of_squarefree
    (D : ℕ) (hD : Squarefree D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
    quadraticOrderPellHalfIntegralCoordinates (D : ℤ)
      (x : rationalQuadraticAlgebra (D : ℤ)) := by
  obtain ⟨t, ht⟩ := rationalQuadraticAlgebra_exists_int_two_mul_re (D : ℤ) x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm (D : ℤ) x
  have him : ∃ b : ℤ, (b : ℚ) =
      2 * (x : rationalQuadraticAlgebra (D : ℤ)).im := by
    apply rat_eq_int_of_squarefree_mul_sq_eq_int hD
    refine ⟨t ^ 2 - 4 * n, ?_⟩
    push_cast
    rw [ht, hn]
    norm_num
    ring
  obtain ⟨b, hb⟩ := him
  exact ⟨t, b, ht, hb⟩

/-- The elementwise containment `2 * 𝓞_K ⊆ ℤ[√D]` in the squarefree
radicand branch. -/
theorem quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_squarefree
    (D : ℕ) (hD : Squarefree D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
    ∃ z : ℤ√(D : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers (D : ℤ) z = (2 : ℤ) • x :=
  (quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_iff
    (D : ℤ) x).mpr
    (quadraticOrderPellHalfIntegralCoordinates_of_squarefree D hD x)

end PellPaper
