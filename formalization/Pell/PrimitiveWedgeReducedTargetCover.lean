import Pell.Main3LargeAnalyticFixedKeyCellTargetLatticeGeometry
import Pell.ReducedDyadicTargetCover
import Pell.SlopeLatticeReciprocalMinimumSize
import Mathlib.Tactic

/-!
# Reduced covers from primitive wedge geometry

A primitive anchor changes integral target coordinates by a determinant-one
matrix.  In those coordinates, the anchor wedge is the second coordinate and
an additive radial functional is triangular.  A radius-two normalization then
feeds directly into the existing reduced-slope coordinate theorem and its
integer-rectangle budgets.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

private theorem main3IntegralTargetWedge_sl2_firstColumn
    (G : SL(2, ℤ)) (x : Fin 2 → ℤ) :
    main3IntegralTargetWedge (fun i ↦ G i 0) (G.toLin' x) = x 1 := by
  have hdet : G 0 0 * G 1 1 - G 0 1 * G 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using G.det_coe
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  simp only [main3IntegralTargetWedge, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc
    G 0 0 * (G 1 0 * x 0 + G 1 1 * x 1) -
          G 1 0 * (G 0 0 * x 0 + G 0 1 * x 1) =
        (G 0 0 * G 1 1 - G 0 1 * G 1 0) * x 1 := by ring
    _ = x 1 := by rw [hdet, one_mul]

private theorem addHom_sl2_inverse_coordinates
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
    ell y = ell (x 0 • (fun i ↦ G i 0) + x 1 • (fun i ↦ G i 1)) :=
      congrArg ell hy
    _ = _ := by
      rw [map_add, map_zsmul, map_zsmul]
      simp only [zsmul_eq_mul, x]

private theorem sl2_mul_toLin_symm_apply
    (G H : SL(2, ℤ)) (y : Fin 2 → ℤ) :
    (G * H).toLin'.symm y = H.toLin'.symm (G.toLin'.symm y) := by
  apply (G * H).toLin'.injective
  simp

/-- A nonempty finite primitive family with bounded anchor wedge and a
comparable positive radial functional admits one actual determinant-one
reduced coordinate system.  The radius-two normalization is chosen so that
the existing full-rectangle budget becomes `36 * C * K`, while its long-side
cost remains the reciprocal first minimum.

The anchor is the first wedge argument and the first column of `G`.  Thus the
final basis is `G * H`, whose inverse acts in the order `H⁻¹ G⁻¹`. -/
theorem exists_primitiveWedge_reducedTargetCover
    (T : Finset (Fin 2 → ℤ)) (ell : (Fin 2 → ℤ) →+ ℝ)
    (y₀ : Fin 2 → ℤ) (R K C : ℝ)
    (hy₀ : y₀ ∈ T)
    (hprimitive : ∀ y ∈ T, IsCoprime (y 0) (y 1))
    (hR : 0 < R) (hK : 0 < K) (hC : 0 < C)
    (hrho : 0 < ell y₀)
    (hradial : ∀ y ∈ T, |ell y| ≤ R)
    (hwedge : ∀ y₁ ∈ T, ∀ y₂ ∈ T,
      |(main3IntegralTargetWedge y₁ y₂ : ℝ)| ≤ K)
    (hcompare : R ≤ C * ell y₀) :
    let rho := ell y₀
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    ∃ G H : SL(2, ℤ),
      (∀ i, G i 0 = y₀ i) ∧
      let beta := ell (fun i ↦ G i 1)
      let z := -K * beta / R
      let mu := firstSlopeSupNorm U V M₀ z
      let delta := M₀ / (U * V)
      let A := 4 / mu
      let B := 4 * mu / delta
      let W := G * H
      slopeVectorSupNorm U V M₀ z (H 0 0, H 1 0) = mu ∧
      (∀ y ∈ T,
        slopeVectorSupNorm U V M₀ z
          (G.toLin'.symm y 0, G.toLin'.symm y 1) ≤ 2) ∧
      1 ≤ M₀ ∧
      0 < mu ∧
      0 < delta ∧
      delta = 4 * rho / (R * K) ∧
      mu ^ 2 ≤ delta ∧
      U * V / M₀ = R * K / (4 * rho) ∧
      U * V / M₀ ≤ C * K / 4 ∧
      A * B = 4 * R * K / rho ∧
      (∀ (S : ℝ) (y : Fin 2 → ℤ),
        slopeVectorSupNorm U V M₀ z
            (G.toLin'.symm y 0, G.toLin'.symm y 1) ≤ S →
          |((W.toLin'.symm y 0 : ℤ) : ℝ)| ≤ 2 * S / mu ∧
          |((W.toLin'.symm y 1 : ℤ) : ℝ)| ≤
            2 * mu * S / delta) ∧
      (sl2InverseTargetImage W T).card = T.card ∧
      (∀ x ∈ sl2InverseTargetImage W T, IsCoprime (x 0) (x 1)) ∧
      (∀ y ∈ T, W.toLin' (W.toLin'.symm y) = y) ∧
      sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A B ∧
      2 ≤ A ∧
      A ≤ 4 * (U + V) ∧
      B ≤ 4 * (U + V) ∧
      (B < 1 → T.card ≤ 2) ∧
      (1 ≤ B →
        ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M₀ ∧
        ((integerSymmetricRectangle A B).card : ℝ) ≤ 36 * C * K ∧
        ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
        ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta ∧
        ((integerSymmetricInterval A).card : ℝ) +
          ((integerSymmetricInterval B).card : ℝ) ≤ 24 / mu) := by
  dsimp only
  let rho := ell y₀
  let U := K / 2
  let V := 1 + C / 2
  let M₀ := 2 * rho * V / R
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hrho' : 0 < rho := by simpa only [rho] using hrho
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  have hM₀one : 1 ≤ M₀ := by
    apply (le_div_iff₀ hR).2
    dsimp only [V]
    nlinarith
  obtain ⟨G, hG00, hG10⟩ := (hprimitive y₀ hy₀).exists_SL2_col 0
  have hGcol : ∀ i, G i 0 = y₀ i := by
    intro i
    fin_cases i
    · exact hG00
    · exact hG10
  let beta := ell (fun i ↦ G i 1)
  let z := -K * beta / R
  let mu := firstSlopeSupNorm U V M₀ z
  let delta := M₀ / (U * V)
  let A := 4 / mu
  let B := 4 * mu / delta
  have hslope : ∀ y ∈ T,
      slopeVectorSupNorm U V M₀ z
        (G.toLin'.symm y 0, G.toLin'.symm y 1) ≤ 2 := by
    intro y hy
    let x := G.toLin'.symm y
    have hell := addHom_sl2_inverse_coordinates ell G y
    change ell y = (x 0 : ℝ) * ell (fun i ↦ G i 0) +
      (x 1 : ℝ) * ell (fun i ↦ G i 1) at hell
    have hell' : ell y = (x 0 : ℝ) * rho + (x 1 : ℝ) * beta := by
      simpa only [rho, beta, hGcol] using hell
    have hwedgeCoord : main3IntegralTargetWedge y₀ y = x 1 := by
      calc
        main3IntegralTargetWedge y₀ y =
            main3IntegralTargetWedge (fun i ↦ G i 0) (G.toLin' x) := by
          rw [G.toLin'.apply_symm_apply]
          congr 1
          funext i
          exact (hGcol i).symm
        _ = x 1 := main3IntegralTargetWedge_sl2_firstColumn G x
    have hfirst : M₀ * (x 0 : ℝ) / V - z * (x 1 : ℝ) / U =
        2 * ell y / R := by
      rw [hell']
      dsimp only [M₀, z, U]
      field_simp [hR.ne', hK.ne', hV.ne']
      ring
    have hsecond : (x 1 : ℝ) / U =
        2 * (main3IntegralTargetWedge y₀ y : ℝ) / K := by
      rw [hwedgeCoord]
      dsimp only [U]
      field_simp [hK.ne']
    rw [slopeVectorSupNorm, hfirst, hsecond]
    apply max_le
    · rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos hR]
      apply (div_le_iff₀ hR).2
      nlinarith [hradial y hy]
    · rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos hK]
      apply (div_le_iff₀ hK).2
      nlinarith [hwedge y₀ hy₀ y hy]
  obtain ⟨H, hfirst, hcoords⟩ :=
    exists_SL2_reduced_slope_coordinates U V M₀ z hU hV hM₀
  have hmu : 0 < mu := by
    exact firstSlopeSupNorm_pos U V M₀ z hU hV hM₀
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaEq : delta = 4 * rho / (R * K) := by
    dsimp only [delta, M₀, U]
    field_simp [hR.ne', hK.ne', hV.ne']
    ring
  have hsq : mu ^ 2 ≤ delta := by
    have hupper := firstSlopeSupNorm_le_sqrt U V M₀ z hU hV hM₀
    have hsqrt := Real.sq_sqrt hdelta.le
    change mu ≤ Real.sqrt delta at hupper
    nlinarith [Real.sqrt_nonneg delta]
  have hratioEq : U * V / M₀ = R * K / (4 * rho) := by
    dsimp only [U, M₀]
    field_simp [hR.ne', hK.ne', hV.ne', hrho'.ne']
    ring
  have hRrho : R / rho ≤ C := (div_le_iff₀ hrho').2 hcompare
  have hratioLe : U * V / M₀ ≤ C * K / 4 := by
    rw [hratioEq]
    calc
      R * K / (4 * rho) = (R / rho) * (K / 4) := by
        field_simp [hrho'.ne']
      _ ≤ C * (K / 4) := by
        exact mul_le_mul_of_nonneg_right hRrho (by positivity)
      _ = C * K / 4 := by ring
  have hanchorNonzero :
      (G.toLin'.symm y₀ 0, G.toLin'.symm y₀ 1) ≠ (0, 0) := by
    intro hzpair
    have hx0 : G.toLin'.symm y₀ 0 = 0 := congrArg Prod.fst hzpair
    have hx1 : G.toLin'.symm y₀ 1 = 0 := congrArg Prod.snd hzpair
    have hp := isCoprime_sl2_inverse_coordinates G y₀ (hprimitive y₀ hy₀)
    rw [hx0, hx1] at hp
    exact not_isCoprime_zero_zero hp
  have hshort : mu ≤ 2 := by
    exact (firstSlopeSupNorm_le U V M₀ z hU hV hM₀
      (G.toLin'.symm y₀ 0, G.toLin'.symm y₀ 1) hanchorNonzero).trans
        (hslope y₀ hy₀)
  have hAtwo : 2 ≤ A := by
    dsimp only [A]
    apply (le_div_iff₀ hmu).2
    nlinarith
  have hreciprocal :=
    reciprocalFirstSlopeSupNorm_le_add U V M₀ z hU hV hM₀one
  have hAcoord : A ≤ 4 * (U + V) := by
    calc
      A = 4 * reciprocalFirstSlopeSupNorm U V M₀ z := by
        dsimp only [A, reciprocalFirstSlopeSupNorm, mu]
        ring
      _ ≤ 4 * (U + V) := by gcongr
  have hBA : B ≤ A := by
    dsimp only [B, A]
    apply (div_le_div_iff₀ hdelta hmu).2
    nlinarith
  have hBcoord : B ≤ 4 * (U + V) := hBA.trans hAcoord
  have hproduct : A * B = 4 * R * K / rho := by
    dsimp only [A, B]
    rw [hdeltaEq]
    field_simp [hmu.ne', hR.ne', hK.ne', hrho'.ne']
  let W := G * H
  have huniversal : ∀ (S : ℝ) (y : Fin 2 → ℤ),
      slopeVectorSupNorm U V M₀ z
          (G.toLin'.symm y 0, G.toLin'.symm y 1) ≤ S →
        |((W.toLin'.symm y 0 : ℤ) : ℝ)| ≤ 2 * S / mu ∧
        |((W.toLin'.symm y 1 : ℤ) : ℝ)| ≤ 2 * mu * S / delta := by
    intro S y hy
    have hc := hcoords S (G.toLin'.symm y) hy
    rw [show W.toLin'.symm y = H.toLin'.symm (G.toLin'.symm y) by
      exact sl2_mul_toLin_symm_apply G H y]
    simpa only [mu, delta] using hc
  have hwidth : ∀ y ∈ T,
      |((W.toLin'.symm y 0 : ℤ) : ℝ)| ≤ A ∧
      |((W.toLin'.symm y 1 : ℤ) : ℝ)| ≤ B := by
    intro y hy
    have hc := huniversal 2 y (hslope y hy)
    dsimp only [A, B]
    constructor
    · convert hc.1 using 1; ring
    · convert hc.2 using 1; ring
  have hsubset : sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_integerSymmetricRectangle A B _).2 (hwidth y hy)
  have hthin : B < 1 → T.card ≤ 2 := by
    exact card_targets_le_two_of_sl2_inverse_thin W T B hprimitive
      (fun y hy ↦ (hwidth y hy).2)
  have hfull : 1 ≤ B →
      ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M₀ ∧
      ((integerSymmetricRectangle A B).card : ℝ) ≤ 36 * C * K ∧
      ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
      ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta ∧
      ((integerSymmetricInterval A).card : ℝ) +
        ((integerSymmetricInterval B).card : ℝ) ≤ 24 / mu := by
    intro hB
    have hbudgets := slope_reduced_integer_rectangle_budgets
      U V M₀ z hU hV hM₀ hshort hB
    have hareaRaw := hbudgets.2.1
    have hareaSharp : ((integerSymmetricRectangle A B).card : ℝ) ≤
        36 * C * K := by
      calc
        ((integerSymmetricRectangle A B).card : ℝ) ≤
            144 * U * V / M₀ := hareaRaw
        _ = 144 * (U * V / M₀) := by ring
        _ ≤ 144 * (C * K / 4) := by gcongr
        _ = 36 * C * K := by ring
    exact ⟨hareaRaw, hareaSharp, hbudgets.2.2.1,
      hbudgets.2.2.2.1, hbudgets.2.2.2.2⟩
  refine ⟨G, H, hGcol, ?_⟩
  refine ⟨hfirst, hslope, hM₀one, hmu, hdelta, hdeltaEq, hsq,
    hratioEq, hratioLe, hproduct, huniversal, card_sl2InverseTargetImage W T,
    primitive_sl2InverseTargetImage W T hprimitive, ?_, hsubset, hAtwo,
    hAcoord, hBcoord, hthin, hfull⟩
  exact fun y _ ↦ W.toLin'.apply_symm_apply y

end

end PellPaper
