import Pell.Main3LargeAnalyticTargetFibrePellInjection

/-!
# Passing a fixed target fibre to its squarefree Pell kernel

The primitive fixed-target surface form has discriminant `w * s^2`, with
`w` the squarefree target parameter of an actual point of the fibre.  This
module rescales the second Pell coordinate by `s`, so that the same finite
source fibre injects into a generalized Pell equation with radicand `w`
rather than the nonsquare discriminant `w * s^2`.

The construction retains the exact nonzero level and exact fibre
cardinality.  No unit-orbit, height-window, representation-number, or
aggregate estimate is asserted here.
-/

namespace PellPaper

noncomputable section

/-- Rescale the second coordinate when a generalized Pell discriminant has
the form `w * s^2`. -/
def generalizedPellSquarefreeKernelMap (s : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (z.1, (s : ℤ) * z.2)

/-- The coordinate rescaling changes the discriminant from `w * s^2` to its
squarefree kernel `w` without changing the represented level. -/
theorem generalizedPellSquarefreeKernelMap_identity
    (w s : ℕ) (z : ℤ × ℤ) :
    (generalizedPellSquarefreeKernelMap s z).1 ^ 2 -
        (w : ℤ) * (generalizedPellSquarefreeKernelMap s z).2 ^ 2 =
      z.1 ^ 2 - ((w * s ^ 2 : ℕ) : ℤ) * z.2 ^ 2 := by
  simp only [generalizedPellSquarefreeKernelMap, Nat.cast_mul, Nat.cast_pow]
  ring

/-- A solution for discriminant `w * s^2` maps to a solution at the same
level for radicand `w`. -/
theorem generalizedPellSquarefreeKernelMap_mem
    {w s : ℕ} {level : ℤ} {z : ℤ × ℤ}
    (hz : z ∈ generalizedPellSolutionFibre
      ((w * s ^ 2 : ℕ) : ℤ) level) :
    generalizedPellSquarefreeKernelMap s z ∈
      generalizedPellSolutionFibre (w : ℤ) level := by
  change z.1 ^ 2 - ((w * s ^ 2 : ℕ) : ℤ) * z.2 ^ 2 = level at hz
  change (generalizedPellSquarefreeKernelMap s z).1 ^ 2 -
      (w : ℤ) * (generalizedPellSquarefreeKernelMap s z).2 ^ 2 = level
  rw [generalizedPellSquarefreeKernelMap_identity]
  exact hz

/-- Rescaling by a positive natural square factor is injective. -/
theorem generalizedPellSquarefreeKernelMap_injective
    {s : ℕ} (hs : 0 < s) :
    Function.Injective (generalizedPellSquarefreeKernelMap s) := by
  intro z z' hzz'
  apply Prod.ext
  · simpa only [generalizedPellSquarefreeKernelMap] using
      congrArg Prod.fst hzz'
  · have hsInt : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
    have hmul : (s : ℤ) * z.2 = (s : ℤ) * z'.2 := by
      simpa only [generalizedPellSquarefreeKernelMap] using
        congrArg Prod.snd hzz'
    exact mul_left_cancel₀ hsInt hmul

/-- A point of the exact target fibre retains the full target dyadic band
in addition to the norm-factorization data used by the primitive-form
discriminant theorem. -/
theorem main3LargeAnalytic_targetFibre_targetNormData_with_dyadicLower
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    ∃ ell w C₀ : ℕ,
      0 < ell ∧ Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < C₀ ∧
        ell ^ 2 ∣ w * C₀ ^ 2 ∧
          shiftedSquareExplicitNormFormEval B.t B.c y =
            ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ) := by
  classical
  obtain ⟨hpImage, hpy⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p).mp hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hpImage
  have heq : main3GeneralBidegreePointVectorEquiv.toEmbedding z =
      (shiftedSquareCoordinatePointSourceVector z,
        shiftedSquareCoordinatePointTargetVector z) :=
    main3GeneralBidegreePointVectorEquiv_apply z
  rw [heq] at hpy
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  change ∃ ell w C₀ : ℕ,
    0 < ell ∧ Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < C₀ ∧
      ell ^ 2 ∣ w * C₀ ^ 2 ∧
        shiftedSquareExplicitNormFormEval B.t B.c y =
          ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ)
  obtain ⟨q, _hq, _hkey, _hcell, _hgeometry, _hcode, hzPackage⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let hY8 : 8 ≤ Y := by omega
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi q
  have hy : y = C.P.y := by
    rw [hzPackage] at hpy
    calc
      y = shiftedSquareCoordinatePointTargetVector
          ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := hpy.symm
      _ = C.P.y := by
        funext j
        fin_cases j <;> rfl
  have hYw : Y ≤ q.1.2.1 := C.scaled.base.target_dyadic.1
  have hwY : q.1.2.1 < 2 * Y := C.scaled.base.target_dyadic.2
  have hwone : 1 < q.1.2.1 := by omega
  refine ⟨C.P.ell, q.1.2.1, C.P.minkowski.C₀,
    C.P.ell_pos, C.scaled.base.target_squarefree, hYw, hwY, hwone,
    C.P.minkowski.C₀_pos, C.P.ell_sq_dvd, ?_⟩
  rw [hy, ← C.t_eq, ← C.c_eq]
  exact C.P.normalized_target_norm

/-- An inhabited exact target fibre fixes a squarefree kernel `w` in the
band `[Y,2Y)` and a positive square factor `s` for the discriminant of its
primitive surface form. -/
theorem main3LargeAnalytic_targetFibre_squarefreeKernelData
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    ∃ w s : ℕ, Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < s ∧
      Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let Q := integralBinaryQuadraticFormPrimitivePart
    (shiftedSquareSurfaceForm B.t B.c y)
  change ∃ w s : ℕ, Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < s ∧
    Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ)
  have hsurface := main3LargeAnalytic_targetFibre_primitive_surfaceForm
    htheta hY hi key cell y p₀.property
  change IsCoprime (p₀.1.1 0) (p₀.1.1 1) ∧
      IsCoprime (y 0) (y 1) ∧
        (shiftedSquareSurfaceForm B.t B.c y).eval
            (p₀.1.1 0) (p₀.1.1 1) =
          shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 at hsurface
  have htargetNorm :=
    main3LargeAnalytic_targetFibre_targetNormData_with_dyadicLower
      htheta hY hi key cell y p₀.property
  change ∃ ell w C₀ : ℕ,
    0 < ell ∧ Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < C₀ ∧
      ell ^ 2 ∣ w * C₀ ^ 2 ∧
        shiftedSquareExplicitNormFormEval B.t B.c y =
          ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ) at htargetNorm
  obtain ⟨ell, w, C₀, hell, hw, hYw, hwY, hwone, hC₀, hdiv, hnorm⟩ :=
    htargetNorm
  have hdisc :=
    shiftedSquareSurfacePrimitivePart_discriminant_pos_not_isSquare
      B.t B.c y hsurface.2.1 B.t_zero_or_one hell hw hwone hC₀ hdiv
        (by simpa only [shiftedSquareExplicitNormFormEval] using hnorm)
  obtain ⟨s, hs, _hscases, hscale⟩ := hdisc.2.2.2.2
  exact ⟨w, s, hw, hYw, hwY, hwone, hs, hscale⟩

/-- Compose the injective leading completion-of-the-square map with the
squarefree-kernel rescaling. -/
noncomputable def main3LargeAnalyticTargetFibreSquarefreeKernelPellMap
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) (s : ℕ)
    (p : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) : ℤ × ℤ :=
  generalizedPellSquarefreeKernelMap s
    (main3LargeAnalyticTargetFibreLeadingPellMap
      htheta hY hi key cell y p)

/-- Under the fixed discriminant factorization, every composite image point
lies on the generalized Pell fibre over the squarefree radicand `w` at the
same level as the unscaled leading-Pell image. -/
theorem main3LargeAnalytic_targetFibreSquarefreeKernelPellMap_mem
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) (w s : ℕ)
    (hdisc :
      (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ))
    (p : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    main3LargeAnalyticTargetFibreSquarefreeKernelPellMap
        htheta hY hi key cell y s p ∈
      generalizedPellSolutionFibre (w : ℤ)
        (4 * (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).a *
          (shiftedSquareAuxiliaryKeySurfaceLevel key /
            (main3LargeAnalyticFixedTargetSurfaceContent hi y : ℤ))) := by
  apply generalizedPellSquarefreeKernelMap_mem
  rw [← hdisc]
  exact
    main3LargeAnalytic_targetFibreLeadingPellMap_mem_generalizedPellSolutionFibre
      htheta hY hi key cell y p

/-- The composite squarefree-kernel map remains injective on the exact target
fibre. -/
theorem main3LargeAnalytic_targetFibreSquarefreeKernelPellMap_injective
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) {s : ℕ} (hs : 0 < s) :
    Function.Injective
      (main3LargeAnalyticTargetFibreSquarefreeKernelPellMap
        htheta hY hi key cell y s) := by
  exact (generalizedPellSquarefreeKernelMap_injective hs).comp
    (main3LargeAnalytic_targetFibreLeadingPellMap_injective
      htheta hY hi key cell y)

/-- The finite squarefree-kernel Pell image of one exact target fibre. -/
noncomputable def main3LargeAnalyticTargetFibreSquarefreeKernelPellImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) (s : ℕ) : Finset (ℤ × ℤ) :=
  (main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y).attach.image
    (main3LargeAnalyticTargetFibreSquarefreeKernelPellMap
      htheta hY hi key cell y s)

/-- Positive square-factor rescaling preserves the exact finite cardinality
of the target fibre. -/
theorem card_main3LargeAnalyticTargetFibreSquarefreeKernelPellImage_eq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) {s : ℕ} (hs : 0 < s) :
    (main3LargeAnalyticTargetFibreSquarefreeKernelPellImage
        htheta hY hi key cell y s).card =
      (main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card := by
  classical
  rw [main3LargeAnalyticTargetFibreSquarefreeKernelPellImage,
    Finset.card_image_of_injective _
      (main3LargeAnalytic_targetFibreSquarefreeKernelPellMap_injective
        htheta hY hi key cell y hs),
    Finset.card_attach]

/-- Every member of the finite composite image lies on the one fixed Pell
fibre over `w`. -/
theorem main3LargeAnalytic_targetFibreSquarefreeKernelPellImage_mem
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) (w s : ℕ)
    (hdisc :
      (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ))
    {z : ℤ × ℤ}
    (hz : z ∈ main3LargeAnalyticTargetFibreSquarefreeKernelPellImage
      htheta hY hi key cell y s) :
    z ∈ generalizedPellSolutionFibre (w : ℤ)
      (4 * (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).a *
        (shiftedSquareAuxiliaryKeySurfaceLevel key /
          (main3LargeAnalyticFixedTargetSurfaceContent hi y : ℤ))) := by
  classical
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hz
  exact main3LargeAnalytic_targetFibreSquarefreeKernelPellMap_mem
    htheta hY hi key cell y w s hdisc p

/-- A chosen point of an inhabited target fibre supplies one squarefree
radicand, one positive square factor, and a finite image of exactly the
original cardinality on a fixed nonzero generalized Pell level. -/
theorem exists_main3LargeAnalytic_targetFibreSquarefreeKernelPellImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
    let level := 4 * Q.a *
      (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ))
    ∃ w s : ℕ, Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < s ∧
      Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) ∧ level ≠ 0 ∧
        (main3LargeAnalyticTargetFibreSquarefreeKernelPellImage
            htheta hY hi key cell y s).card =
          (main3LargeAnalyticFixedKeyCellTargetFibre
            htheta hY hi key cell y).card ∧
        ∀ z ∈ main3LargeAnalyticTargetFibreSquarefreeKernelPellImage
            htheta hY hi key cell y s,
          z ∈ generalizedPellSolutionFibre (w : ℤ) level := by
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
  let level := 4 * Q.a *
    (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ))
  have hkernel := main3LargeAnalytic_targetFibre_squarefreeKernelData
    htheta hY hi key cell y p₀
  change ∃ w s : ℕ, Squarefree w ∧ Y ≤ w ∧ w < 2 * Y ∧ 1 < w ∧ 0 < s ∧
    Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) at hkernel
  obtain ⟨w, s, hw, hYw, hwY, hwone, hs, hdisc⟩ := hkernel
  have hparameters := main3LargeAnalytic_targetFibreLeadingPell_parameters
    htheta hY hi key cell y p₀
  change 0 < Q.discriminant ∧ ¬ IsSquare Q.discriminant ∧ Q.a ≠ 0 ∧
    level ≠ 0 at hparameters
  refine ⟨w, s, hw, hYw, hwY, hwone, hs, hdisc, hparameters.2.2.2,
    card_main3LargeAnalyticTargetFibreSquarefreeKernelPellImage_eq
      htheta hY hi key cell y hs, ?_⟩
  intro z hz
  exact main3LargeAnalytic_targetFibreSquarefreeKernelPellImage_mem
    htheta hY hi key cell y w s hdisc hz

end

end PellPaper
