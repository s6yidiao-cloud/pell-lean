import Pell.Main3LargeAnalyticComplexCoverShortestVectorBound
import Mathlib.Tactic

/-!
# Complex reduced-cover short-vector radius candidate

This file converts the existing squared reciprocal-band estimate into the
literal Euclidean radius bound needed by finite lattice-ball incidence.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

local instance main3LargeAnalyticComplexShortVectorRadius_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Removing the harmless factor `5/8` and taking nonnegative square roots
turns the squared band estimate into radius `sqrt(E)/S`. -/
theorem norm_le_sqrt_div_of_sq_le_five_eighth_div_sq
    {x E S : ℝ} (hx : 0 ≤ x) (hE : 0 ≤ E) (hS : 0 < S)
    (hsq : x ^ 2 ≤ ((5 / 8 : ℝ) * E) / S ^ 2) :
    x ≤ Real.sqrt E / S := by
  have hright : 0 ≤ Real.sqrt E / S := div_nonneg (Real.sqrt_nonneg E) hS.le
  apply (sq_le_sq₀ hx hright).mp
  calc
    x ^ 2 ≤ ((5 / 8 : ℝ) * E) / S ^ 2 := hsq
    _ ≤ E / S ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg S)
      nlinarith
    _ = (Real.sqrt E / S) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hE]

/-- Every exact reduced cover places its reciprocal first minimum between
`1/2` and the common coarse endpoint `U+V`.  Both bounds are already latent
in the cover's `A = 4/mu` interval estimates. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.reciprocal_firstSlopeSupNorm_mem_interval
    {T : Finset (Fin 2 → ℤ)} {ell : (Fin 2 → ℤ) →+ ℝ}
    {y₀ : Fin 2 → ℤ} {R K C : ℝ} {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      T ell y₀ R K C G H) :
    let rho := ell y₀
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := ell (fun i ↦ G i 1)
    let z := -K * beta / R
    let mu := firstSlopeSupNorm U V M₀ z
    (1 / 2 : ℝ) ≤ 1 / mu ∧ 1 / mu ≤ U + V := by
  unfold PrimitiveWedgeReducedTargetCoverSpec at hspec
  dsimp only at hspec ⊢
  rcases hspec with
    ⟨_hcolumn, _hminimum, _hall, _hM₀, _hmu, _hdelta, _hdeltaEq,
      _hmuSq, _hratioEq, _hratioLe, _hproduct, _huniversal,
      _hcard, _hprimitive, _hrecover, _hsubset, hAtwo, hA, _hB,
      _hthin, _hfull⟩
  constructor
  · rw [show 4 / firstSlopeSupNorm (K / 2) (1 + C / 2)
        (2 * ell y₀ * (1 + C / 2) / R)
        (-K * ell (fun i ↦ G i 1) / R) =
      4 * (1 / firstSlopeSupNorm (K / 2) (1 + C / 2)
        (2 * ell y₀ * (1 + C / 2) / R)
        (-K * ell (fun i ↦ G i 1) / R)) by ring] at hAtwo
    linarith
  · rw [show 4 / firstSlopeSupNorm (K / 2) (1 + C / 2)
        (2 * ell y₀ * (1 + C / 2) / R)
        (-K * ell (fun i ↦ G i 1) / R) =
      4 * (1 / firstSlopeSupNorm (K / 2) (1 + C / 2)
        (2 * ell y₀ * (1 + C / 2) / R)
        (-K * ell (fun i ↦ G i 1) / R)) by ring] at hA
    linarith

/-- The exact complex reduced-cover shortest vector lies in the fixed-basis
ball of radius `sqrt(E)/S` throughout a positive reciprocal-minimum band. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.complex_shortest_original_vector_norm_le_sqrt_div
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a)
    {T : Finset (Fin 2 → ℤ)} {E Mmesh S : ℝ}
    (hE : 0 < E) (hMmesh : 6 ≤ Mmesh) (hS : 0 < S)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T E
      ((6 * E / Mmesh) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) 2)
    (hell : cert.ell = main3AnchorHermitianRadialAddHom 1
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) cert.anchor)
    (hrhoLower : E ≤ 2 * cert.ell cert.anchor)
    {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      T cert.ell cert.anchor E
        ((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 2 G H)
    (hband : S ≤ 1 /
      firstSlopeSupNorm
        ((((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|)) / 2)
        (1 + (2 : ℝ) / 2)
        (2 * cert.ell cert.anchor * (1 + (2 : ℝ) / 2) / E)
        (-(((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|)) *
          cert.ell (fun i ↦ G i 1) / E)) :
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    ‖main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ≤
        Real.sqrt E / S := by
  dsimp only
  have hsq :=
    (hspec.complex_shortest_original_vector_norm_sq_bounds
      F ha hE hMmesh cert hell hrhoLower).2.2 S hS hband
  exact norm_le_sqrt_div_of_sq_le_five_eighth_div_sq
    (norm_nonneg _) hE.le hS hsq

end

end PellPaper
