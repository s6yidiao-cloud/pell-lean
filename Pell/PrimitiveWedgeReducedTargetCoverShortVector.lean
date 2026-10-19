import Pell.Main3LargeAnalyticFixedKeyCellTargetRadialGeometry
import Mathlib.Tactic

/-!
# Pulling a reduced first minimum back to original target coordinates

The primitive-wedge construction writes the normalized slope coordinates in
an integral basis whose first column is the chosen primitive anchor.  This
module records the exact coordinate identity and identifies the first column
of the final product basis as a primitive original-coordinate vector attaining
the displayed first minimum.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- The first column of the final product basis, regarded in the original
integral target coordinates. -/
def primitiveWedgeReducedTargetCoverShortestVector
    (G H : SL(2, ℤ)) : Fin 2 → ℤ :=
  fun i ↦ (G * H) i 0

private theorem main3IntegralTargetWedge_sl2_firstColumn_shortVector
    (G : SL(2, ℤ)) (x : Fin 2 → ℤ) :
    main3IntegralTargetWedge (fun i ↦ G i 0) (G.toLin' x) = x 1 := by
  have hdet : G 0 0 * G 1 1 - G 0 1 * G 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using G.det_coe
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  simp only [main3IntegralTargetWedge, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  calc
    G 0 0 * (G 1 0 * x 0 + G 1 1 * x 1) -
          G 1 0 * (G 0 0 * x 0 + G 0 1 * x 1) =
        (G 0 0 * G 1 1 - G 0 1 * G 1 0) * x 1 := by ring
    _ = x 1 := by rw [hdet, one_mul]

private theorem addHom_sl2_inverse_coordinates_shortVector
    (ell : (Fin 2 → ℤ) →+ ℝ) (G : SL(2, ℤ)) (y : Fin 2 → ℤ) :
    let x := G.toLin'.symm y
    ell y = (x 0 : ℝ) * ell (fun i ↦ G i 0) +
      (x 1 : ℝ) * ell (fun i ↦ G i 1) := by
  let x := G.toLin'.symm y
  have hy : y = x 0 • (fun i ↦ G i 0) + x 1 • (fun i ↦ G i 1) := by
    rw [← G.toLin'.apply_symm_apply y]
    change G.toLin' x = _
    funext i
    change Matrix.mulVec G.1 x i = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  change ell y = _
  calc
    ell y = ell (x 0 • (fun i ↦ G i 0) +
        x 1 • (fun i ↦ G i 1)) := congrArg ell hy
    _ = _ := by
      rw [map_add, map_zsmul, map_zsmul]
      simp only [zsmul_eq_mul, x]

/-- In a determinant-one basis whose first column is `y₀`, the slope norm
is exactly the maximum of the normalized radial functional and normalized
anchor wedge.  This is an identity for every original-coordinate vector, not
only for vectors in the finite target set. -/
theorem slopeVectorSupNorm_anchor_inverse_coordinates_eq
    (ell : (Fin 2 → ℤ) →+ ℝ) (y₀ : Fin 2 → ℤ)
    (R K C : ℝ) (G : SL(2, ℤ))
    (hcolumn : ∀ i, G i 0 = y₀ i)
    (hR : R ≠ 0) (hK : K ≠ 0) (hV : 1 + C / 2 ≠ 0)
    (y : Fin 2 → ℤ) :
    let rho := ell y₀
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := ell (fun i ↦ G i 1)
    let z := -K * beta / R
    slopeVectorSupNorm U V M₀ z
        (G.toLin'.symm y 0, G.toLin'.symm y 1) =
      max |2 * ell y / R|
        |2 * (main3IntegralTargetWedge y₀ y : ℝ) / K| := by
  dsimp only
  let x := G.toLin'.symm y
  let rho := ell y₀
  let beta := ell (fun i ↦ G i 1)
  have hell := addHom_sl2_inverse_coordinates_shortVector ell G y
  change ell y = (x 0 : ℝ) * ell (fun i ↦ G i 0) +
    (x 1 : ℝ) * ell (fun i ↦ G i 1) at hell
  have hell' : ell y = (x 0 : ℝ) * rho + (x 1 : ℝ) * beta := by
    simpa only [rho, beta, hcolumn] using hell
  have hwedge : main3IntegralTargetWedge y₀ y = x 1 := by
    calc
      main3IntegralTargetWedge y₀ y =
          main3IntegralTargetWedge (fun i ↦ G i 0) (G.toLin' x) := by
        rw [G.toLin'.apply_symm_apply]
        congr 1
        funext i
        exact (hcolumn i).symm
      _ = x 1 :=
        main3IntegralTargetWedge_sl2_firstColumn_shortVector G x
  have hfirst :
      (2 * rho * (1 + C / 2) / R) * (x 0 : ℝ) /
            (1 + C / 2) -
          (-K * beta / R) * (x 1 : ℝ) / (K / 2) =
        2 * ell y / R := by
    rw [hell']
    have htwoC : 2 + C ≠ 0 := by
      intro hc
      apply hV
      rw [show 1 + C / 2 = (2 + C) / 2 by ring, hc, zero_div]
    field_simp [hR, hK, hV, htwoC]
    ring
  have hsecond : (x 1 : ℝ) / (K / 2) =
      2 * (main3IntegralTargetWedge y₀ y : ℝ) / K := by
    rw [hwedge]
    field_simp [hK]
  rw [slopeVectorSupNorm, hfirst, hsecond]

private theorem sl2_firstColumn_pullback_shortVector
    (G H : SL(2, ℤ)) :
    G.toLin'.symm (primitiveWedgeReducedTargetCoverShortestVector G H) =
      fun i ↦ H i 0 := by
  apply G.toLin'.injective
  rw [G.toLin'.apply_symm_apply]
  funext i
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  simp only [primitiveWedgeReducedTargetCoverShortestVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

/-- The reduced-cover specification contains a literal primitive nonzero
original-coordinate vector attaining `mu`.  It is the first column of
`W = G * H`, and its exact radial/wedge norm is exposed for downstream
quadratic-order short-vector counting. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.shortest_original_vector
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
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    y ≠ 0 ∧ IsCoprime (y 0) (y 1) ∧
      max |2 * ell y / R|
          |2 * (main3IntegralTargetWedge y₀ y : ℝ) / K| = mu := by
  unfold PrimitiveWedgeReducedTargetCoverSpec at hspec
  dsimp only at hspec ⊢
  rcases hspec with
    ⟨hcolumn, hminimum, _hall, hM₀, _hmu, hdelta, _hdeltaEq,
      _hmuSq, _hratioEq, _hratioLe, _hproduct, _huniversal,
      _hcard, _hprimitive, _hrecover, _hsubset, _hAtwo, _hA, _hB,
      _hthin, _hfull⟩
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  have hcop : IsCoprime (y 0) (y 1) := by
    simpa only [y, primitiveWedgeReducedTargetCoverShortestVector] using
      Matrix.SpecialLinearGroup.isCoprime_col (G * H) 0
  have hyne : y ≠ 0 := by
    intro hy
    have hy0 : y 0 = 0 := congrFun hy 0
    have hy1 : y 1 = 0 := congrFun hy 1
    rw [hy0, hy1] at hcop
    exact not_isCoprime_zero_zero hcop
  refine ⟨hyne, hcop, ?_⟩
  have hpull : G.toLin'.symm y = fun i ↦ H i 0 := by
    simpa only [y] using sl2_firstColumn_pullback_shortVector G H
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hM₀
    norm_num at hM₀
  have hK : K ≠ 0 := by
    intro hzero
    rw [hzero] at hdelta
    norm_num at hdelta
  have hV : 1 + C / 2 ≠ 0 := by
    intro hzero
    rw [hzero] at hdelta
    norm_num at hdelta
  have hid := slopeVectorSupNorm_anchor_inverse_coordinates_eq
    ell y₀ R K C G hcolumn hR hK hV y
  dsimp only at hid
  rw [hpull] at hid
  exact hid.symm.trans hminimum

end

end PellPaper
