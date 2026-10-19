import Pell.Main3LargeAnalyticComplexShortVectorCellMultiplicity
import Pell.Main3LargeAnalyticComplexShortVectorRadius
import Pell.FiniteFixedVectorFiberWeightedIncidence
import Pell.Main3LargeAnalyticComplexCellCoverSelection
import Mathlib.Tactic

/-!
# Main3 complex reciprocal-minimum band incidence candidate

This file assembles the reviewed geometric and finite-summation interfaces
around the literal fixed-basis complex norm.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticComplexShortVectorBandIncidence_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Filtering the image of any nonzero fixed-basis vector assignment by its
complex norm inherits the linear-plus-area lattice-ball estimate. -/
theorem card_fixedBasisVectorImage_filter_norm_le_linear_add_area
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a) (ha : 0 < a)
    (I : Finset ι) (f : ι → Fin 2 → ℤ)
    (hnonzero : ∀ i ∈ I, f i ≠ 0)
    (t : ℝ) (ht : 1 ≤ t) :
    ((((I.image f).filter fun y =>
        ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ≤ t).card : ℕ) : ℝ) ≤
      12 * t + (72 /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) * t ^ 2 := by
  classical
  let V := (I.image f).filter fun y =>
    ‖main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ≤ t
  have hcount :=
    card_shiftedSquareFixedBasis_imaginaryPlace_norm_le_linear_add_area
      ha F V t ht
        (by
          intro y hy
          have hyImage := (Finset.mem_filter.mp hy).1
          obtain ⟨i, hi, hify⟩ := Finset.mem_image.mp hyImage
          rw [← hify]
          exact hnonzero i hi)
        (by
          intro y hy
          exact (Finset.mem_filter.mp hy).2)
  calc
    (((V.card : ℕ) : ℝ)) ≤ 12 * t + 72 * t ^ 2 /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)| := hcount
    _ = 12 * t + (72 /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) * t ^ 2 := by ring

/-- Every label occurring in the image of a nonzero fixed-basis assignment
has complex norm at least one. -/
theorem one_le_norm_fixedBasisVectorImage
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a) (ha : 0 < a)
    (I : Finset ι) (f : ι → Fin 2 → ℤ)
    (hnonzero : ∀ i ∈ I, f i ≠ 0) :
    ∀ y ∈ I.image f,
      1 ≤ ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ := by
  intro y hy
  obtain ⟨i, hi, hify⟩ := Finset.mem_image.mp hy
  rw [← hify]
  exact one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
    ha F (f i) (hnonzero i hi)

/-- The cover determinant relation supplies the stronger Minkowski cutoff
`sqrt(K)/2` for every selected complex reciprocal minimum. -/
theorem Main3LargeAnalyticComplexCellCoverSelectionData.sqrt_K_div_two_le_reciprocal_mu
    {T : Finset (Fin 2 → ℤ)} {omega : ℂ}
    {E Delta Mmesh K T₀ A Y : ℝ}
    (Q : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y) :
    Real.sqrt K / 2 ≤ 1 / Q.mu := by
  have hspec := Q.cover_spec
  unfold PrimitiveWedgeReducedTargetCoverSpec at hspec
  dsimp only at hspec
  rcases hspec with
    ⟨_hcolumn, _hminimum, _hall, _hM₀one, _hmu, _hdelta,
      _hdeltaEq, hmuSq, _hratioEq, _hratioLe, _hproduct,
      _huniversal, _hcard, _hprimitive, _hrecover, _hsubset,
      _hAtwo, _hA, _hB, _hthin, _hfull⟩
  have hmuSqQ : Q.mu ^ 2 ≤ Q.M₀ / (Q.U * Q.V) := by
    simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.mu,
      Main3LargeAnalyticComplexCellCoverSelectionData.U,
      Main3LargeAnalyticComplexCellCoverSelectionData.V,
      Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
      Main3LargeAnalyticComplexCellCoverSelectionData.rho,
      Main3LargeAnalyticComplexCellCoverSelectionData.z,
      Main3LargeAnalyticComplexCellCoverSelectionData.beta] using hmuSq
  have hK : 0 < K := Q.cert.K_pos
  have hUV : Q.U * Q.V = K := by
    dsimp only [Main3LargeAnalyticComplexCellCoverSelectionData.U,
      Main3LargeAnalyticComplexCellCoverSelectionData.V]
    ring
  have hM₀Upper : Q.M₀ ≤ 4 := by
    simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
      Main3LargeAnalyticComplexCellCoverSelectionData.rho,
      Main3LargeAnalyticComplexCellCoverSelectionData.V] using
        Q.calibration.2.2.2.1
  have hKmuSq : K * Q.mu ^ 2 ≤ 4 := by
    calc
      K * Q.mu ^ 2 ≤ K * (Q.M₀ / (Q.U * Q.V)) := by gcongr
      _ = Q.M₀ := by rw [hUV]; field_simp [hK.ne']
      _ ≤ 4 := hM₀Upper
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hprodNonneg : 0 ≤ Real.sqrt K * Q.mu :=
    mul_nonneg hsqrtK.le Q.mu_pos.le
  have hprodSq : (Real.sqrt K * Q.mu) ^ 2 ≤ 2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK.le]
    norm_num
    exact hKmuSq
  have hprod : Real.sqrt K * Q.mu ≤ 2 :=
    (sq_le_sq₀ hprodNonneg (by norm_num)).mp hprodSq
  apply (le_div_iff₀ Q.mu_pos).2
  nlinarith

/-- Elementary square-root algebra for the area contribution after using
the stronger cutoff `sqrt(6E/(M*Delta))/2`. -/
theorem div_sqrt_six_scaled_ratio_le_sqrt_product
    {E M Delta : ℝ} (hE : 0 < E) (hM : 0 < M)
    (hDelta : 0 < Delta) :
    E / Delta / Real.sqrt (6 * E / (M * Delta)) ≤
      Real.sqrt (E * M / Delta) := by
  have hK : 0 < 6 * E / (M * Delta) := by positivity
  have hX : 0 ≤ E * M / Delta := by positivity
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, div_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hX]
  field_simp [hE.ne', hM.ne', hDelta.ne']
  nlinarith

/-! ## Exact selected Main3 data -/

/-- The globally defined shortest-vector label is nontrivial precisely on
the active complex cells; outside that finite set it is set to zero. -/
noncomputable def main3LargeAnalytic_selectedComplexCellShortestVector
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (cell : ComplexUnitCircleSlopeCellIndex) : Fin 2 → ℤ :=
  if hcell : cell ∈
      main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key then
    (main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha ⟨cell, hcell⟩).shortestVector
  else 0

/-- The reciprocal-minimum parameter attached to the same selected complex
cover, extended by the harmless value one outside the active cells. -/
noncomputable def main3LargeAnalytic_selectedComplexCellMu
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (cell : ComplexUnitCircleSlopeCellIndex) : ℝ :=
  if hcell : cell ∈
      main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key then
    (main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha ⟨cell, hcell⟩).mu
  else 1

/-- Active complex cells in a reciprocal-minimum tail. -/
noncomputable def main3LargeAnalytic_complexCellReciprocalMinimumBand
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v) (S : ℝ) :
    Finset ComplexUnitCircleSlopeCellIndex :=
  (main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key).filter
    fun cell => S ≤ 1 /
      main3LargeAnalytic_selectedComplexCellMu htheta hY hi key ha cell

@[simp]
theorem mem_main3LargeAnalytic_complexCellReciprocalMinimumBand
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v) (S : ℝ)
    (cell : ComplexUnitCircleSlopeCellIndex) :
    cell ∈ main3LargeAnalytic_complexCellReciprocalMinimumBand
        htheta hY hi key ha S ↔
      cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key ∧
      S ≤ 1 / main3LargeAnalytic_selectedComplexCellMu
        htheta hY hi key ha cell := by
  classical
  simp [main3LargeAnalytic_complexCellReciprocalMinimumBand]

/-! ## The literal complex band count -/

/-- On every positive reciprocal-minimum threshold for which the induced
short-vector radius is at least one, the literal active Main3 complex cells
obey the weighted fixed-basis lattice-incidence estimate. -/
theorem card_main3LargeAnalytic_complexCellReciprocalMinimumBand_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (S : ℝ) (hS : 0 < S)
    (hH : 1 ≤ Real.sqrt
      (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) / S) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Hrad := Real.sqrt E / S
    ((main3LargeAnalytic_complexCellReciprocalMinimumBand
      htheta hY hi key ha S).card : ℝ) ≤
      9216 * Hrad * (2 + Real.log Hrad) +
        165888 * Hrad ^ 2 / Delta := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let f : ComplexUnitCircleSlopeCellIndex → Fin 2 → ℤ :=
    main3LargeAnalytic_selectedComplexCellShortestVector
      htheta hY hi key ha
  let mu : ComplexUnitCircleSlopeCellIndex → ℝ :=
    main3LargeAnalytic_selectedComplexCellMu htheta hY hi key ha
  let J := main3LargeAnalytic_complexCellReciprocalMinimumBand
    htheta hY hi key ha S
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Hrad := Real.sqrt E / S
  let r : (Fin 2 → ℤ) → ℝ := fun y =>
    ‖main3IntegralTargetLinearForm (sigma F.omega) y‖
  have hM : 0 < main3UnbalancedM theta Y :=
    lt_of_lt_of_le (by omega) (six_le_main3UnbalancedM htheta hY)
  have hMreal : (6 : ℝ) ≤ (main3UnbalancedM theta Y : ℝ) := by
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hJI : J ⊆
      main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key := by
    intro cell hcell
    exact (mem_main3LargeAnalytic_complexCellReciprocalMinimumBand
      htheta hY hi key ha S cell).mp hcell |>.1
  have hnonzero : ∀ cell ∈ J, f cell ≠ 0 := by
    intro cell hcell
    have hcellI := hJI hcell
    let c : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key) := ⟨cell, hcellI⟩
    let Q := main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha c
    simpa only [f, main3LargeAnalytic_selectedComplexCellShortestVector,
      dif_pos hcellI, c, Q] using Q.shortestVector_spec.1
  have hrLower : ∀ y ∈ J.image f, 1 ≤ r y := by
    simpa only [r] using
      one_le_norm_fixedBasisVectorImage F ha J f hnonzero
  have hrUpper : ∀ y ∈ J.image f, r y ≤ Hrad := by
    intro y hy
    obtain ⟨cell, hcell, hfcell⟩ := Finset.mem_image.mp hy
    have hcellBand :=
      (mem_main3LargeAnalytic_complexCellReciprocalMinimumBand
        htheta hY hi key ha S cell).mp hcell
    have hcellI : cell ∈
        main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key :=
      hcellBand.1
    let c : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key) := ⟨cell, hcellI⟩
    let Q := main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha c
    have hbandQ : S ≤ 1 / Q.mu := by
      simpa only [mu, main3LargeAnalytic_selectedComplexCellMu,
        dif_pos hcellI, c, Q] using hcellBand.2
    have hrad :=
      Q.cover_spec.complex_shortest_original_vector_norm_le_sqrt_div
        F ha Q.cert.R_pos hMreal hS Q.cert Q.ell_eq Q.rho_lower hbandQ
    rw [← hfcell]
    simpa only [r, Hrad, E, sigma, F, f,
      main3LargeAnalytic_selectedComplexCellShortestVector,
      dif_pos hcellI, c, Q,
      Main3LargeAnalyticComplexCellCoverSelectionData.shortestVector] using hrad
  have hball : ∀ t : ℝ, 1 ≤ t → t ≤ Hrad →
      ((((J.image f).filter fun y => r y ≤ t).card : ℕ) : ℝ) ≤
        12 * t + (72 / Delta) * t ^ 2 := by
    intro t ht _htH
    simpa only [r, Delta, sigma, F] using
      card_fixedBasisVectorImage_filter_norm_le_linear_add_area
        F ha J f hnonzero t ht
  have hfiber : ∀ y ∈ J.image f,
      (((J.filter fun cell => f cell = y).card : ℕ) : ℝ) ≤
        140 + 768 * Hrad / r y := by
    intro y hy
    let C := J.filter fun cell => f cell = y
    have hCI : C ⊆
        main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key := by
      intro cell hcell
      exact hJI (Finset.mem_filter.mp hcell).1
    let active : ↑C →
        ↑(main3LargeAnalytic_nonemptyComplexCellIndices
          htheta hY hi key) := fun c => ⟨c.1, hCI c.2⟩
    let Q : (c : ↑C) →
        Main3LargeAnalyticFixedKeyComplexCellCoverSelection
          htheta hY hi key c.1 ha := fun c =>
      main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha (active c)
    have hCindices : C ⊆ complexUnitCircleSlopeCellIndices
        (main3UnbalancedM theta Y) := by
      intro cell hcell
      exact (mem_main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key cell).mp (hCI hcell) |>.1
    have hcommon :=
      card_complexUnitCircleSlopeCells_with_common_shortestVector_le
        F ha hM hS y C hCindices
        (fun c => main3LargeAnalyticFixedKeyCellTargetVectorImage
          htheta hY hi key (Sum.inr c.1))
        (fun c => (Q c).cert)
        (fun c => (Q c).ell_eq)
        (fun c => (Q c).rho_lower)
        (fun c => (Q c).rho_upper)
        (fun c => (Q c).G) (fun c => (Q c).H)
        (fun c => (Q c).cover_spec)
        (fun c => by
          have hcJ := (Finset.mem_filter.mp c.2).1
          have hcBand :=
            (mem_main3LargeAnalytic_complexCellReciprocalMinimumBand
              htheta hY hi key ha S c.1).mp hcJ
          simpa only [mu, main3LargeAnalytic_selectedComplexCellMu,
            dif_pos (hCI c.2), active, Q,
            Main3LargeAnalyticComplexCellCoverSelectionData.mu,
            Main3LargeAnalyticComplexCellCoverSelectionData.U,
            Main3LargeAnalyticComplexCellCoverSelectionData.V,
            Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
            Main3LargeAnalyticComplexCellCoverSelectionData.rho,
            Main3LargeAnalyticComplexCellCoverSelectionData.z,
            Main3LargeAnalyticComplexCellCoverSelectionData.beta]
            using hcBand.2)
        (fun c => by
          have hcy := (Finset.mem_filter.mp c.2).2
          simpa only [f, main3LargeAnalytic_selectedComplexCellShortestVector,
            dif_pos (hCI c.2), active, Q,
            Main3LargeAnalyticComplexCellCoverSelectionData.shortestVector]
            using hcy)
        (fun c => by
          exact
            main3LargeAnalyticFixedKeyComplexCellTargetVector_direction_mem_tube
              htheta hY hi key c.1 ha (Q c).cert.anchor_mem)
    calc
      (((J.filter fun cell => f cell = y).card : ℕ) : ℝ) ≤
          140 + 768 * Real.sqrt E /
            (S * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖) := by
        simpa only [C, E, sigma, F] using hcommon
      _ = 140 + 768 * Hrad / r y := by
        dsimp only [Hrad, r]
        ring
  simpa only [J, f, r, Hrad, Delta] using
    card_le_complexFixedVectorRadialWeightedImage
      J f r Hrad Delta hH hDelta hrLower hrUpper hball hfiber

/-- The exact band count in weak reciprocal-linear plus reciprocal-square
form, uniformly for every threshold at least `1/2`.  When the induced ball
radius is below one the band is empty by integrality. -/
theorem card_main3LargeAnalytic_complexCellReciprocalMinimumBand_le_weakTail
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (hE : 0 < main3LargeAnalyticFixedKeyTargetScaleUpper Y key)
    (hH₀ : 1 ≤ 2 * Real.sqrt
      (main3LargeAnalyticFixedKeyTargetScaleUpper Y key))
    (T : ℝ) (hT : (1 / 2 : ℝ) ≤ T) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let H₀ := 2 * Real.sqrt E
    let A := 9216 * Real.sqrt E * (2 + Real.log H₀)
    let B := 165888 * E / Delta
    ((main3LargeAnalytic_complexCellReciprocalMinimumBand
      htheta hY hi key ha T).card : ℝ) ≤ A / T + B / T ^ 2 := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let H₀ := 2 * Real.sqrt E
  let Hrad := Real.sqrt E / T
  let Acoef := 9216 * Real.sqrt E * (2 + Real.log H₀)
  let Bcoef := 165888 * E / Delta
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hHradUpper : Hrad ≤ H₀ := by
    dsimp only [Hrad, H₀]
    apply (div_le_iff₀ hTpos).2
    have hsqrt := Real.sqrt_nonneg E
    nlinarith
  have hH₀pos : 0 < H₀ := zero_lt_one.trans_le (by simpa only [H₀, E] using hH₀)
  have hlogH₀ : 0 ≤ Real.log H₀ :=
    Real.log_nonneg (by simpa only [H₀, E] using hH₀)
  have hAcoef : 0 ≤ Acoef := by
    dsimp only [Acoef]
    positivity
  have hBcoef : 0 ≤ Bcoef := by
    dsimp only [Bcoef]
    positivity
  by_cases hHrad : 1 ≤ Hrad
  · have hcount :=
      card_main3LargeAnalytic_complexCellReciprocalMinimumBand_le
        htheta hY hi key ha T hTpos (by simpa only [Hrad, E] using hHrad)
    have hlog : Real.log Hrad ≤ Real.log H₀ :=
      Real.log_le_log (zero_lt_one.trans_le hHrad) hHradUpper
    calc
      ((main3LargeAnalytic_complexCellReciprocalMinimumBand
          htheta hY hi key ha T).card : ℝ) ≤
          9216 * Hrad * (2 + Real.log Hrad) +
            165888 * Hrad ^ 2 / Delta := by
        simpa only [E, Delta, Hrad] using hcount
      _ ≤ 9216 * Hrad * (2 + Real.log H₀) +
            165888 * Hrad ^ 2 / Delta := by
        gcongr
      _ = Acoef / T + Bcoef / T ^ 2 := by
        dsimp only [Hrad, Acoef, Bcoef]
        rw [div_pow, Real.sq_sqrt (by simpa only [E] using hE.le)]
        field_simp [hTpos.ne', hDelta.ne']
  · have hempty : main3LargeAnalytic_complexCellReciprocalMinimumBand
        htheta hY hi key ha T = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      obtain ⟨cell, hcell⟩ := hnonempty
      have hcellBand :=
        (mem_main3LargeAnalytic_complexCellReciprocalMinimumBand
          htheta hY hi key ha T cell).mp hcell
      have hcellI := hcellBand.1
      let c : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key) := ⟨cell, hcellI⟩
      let Q := main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha c
      have hbandQ : T ≤ 1 / Q.mu := by
        simpa only [main3LargeAnalytic_selectedComplexCellMu,
          dif_pos hcellI, c, Q] using hcellBand.2
      have hupper :=
        Q.cover_spec.complex_shortest_original_vector_norm_le_sqrt_div
          F ha Q.cert.R_pos
            (by exact_mod_cast six_le_main3UnbalancedM htheta hY)
          hTpos Q.cert Q.ell_eq Q.rho_lower hbandQ
      have hlower :=
        one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
          ha F Q.shortestVector Q.shortestVector_spec.1
      have hone : (1 : ℝ) ≤ Hrad := by
        exact hlower.trans (by
          simpa only [Hrad, E, sigma, F,
            Main3LargeAnalyticComplexCellCoverSelectionData.shortestVector]
            using hupper)
      exact hHrad hone
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact add_nonneg (div_nonneg hAcoef hTpos.le)
      (div_nonneg hBcoef (sq_nonneg T))

/-- Summing the reciprocal first minima over all active complex cells gives
the manuscript's two-log intrinsic lattice budget.  The first logarithm is
the radial partial-summation loss and the second is the finite tail range. -/
theorem sum_main3LargeAnalytic_nonemptyComplexCell_reciprocalMinimum_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let K := (6 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
    let S₀ := max (1 / 2 : ℝ) (Real.sqrt K / 2)
    let L := K / 2 + 2
    let H₀ := 2 * Real.sqrt E
    let A := 9216 * Real.sqrt E * (2 + Real.log H₀)
    let B := 165888 * E / Delta
    (∑ cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedComplexCellMu
        htheta hY hi key ha cell) ≤
      A * (1 + Real.log (L / S₀)) + 2 * B / S₀ := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
  let r : ComplexUnitCircleSlopeCellIndex → ℝ := fun cell =>
    1 / main3LargeAnalytic_selectedComplexCellMu
      htheta hY hi key ha cell
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let K := (6 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
  let S₀ := max (1 / 2 : ℝ) (Real.sqrt K / 2)
  let L := K / 2 + 2
  let H₀ := 2 * Real.sqrt E
  let Acoef := 9216 * Real.sqrt E * (2 + Real.log H₀)
  let Bcoef := 165888 * E / Delta
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  let Q₀ := main3LargeAnalytic_complexCellCoverSelection
    htheta hY hi key ha c₀
  have hE : 0 < E := by
    simpa only [E] using Q₀.cert.R_pos
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hMreal : (6 : ℝ) ≤ (main3UnbalancedM theta Y : ℝ) := by
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hend₀ := Q₀.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
  have hhalf₀ : (1 / 2 : ℝ) ≤ 1 / Q₀.mu := by
    simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.mu,
      Main3LargeAnalyticComplexCellCoverSelectionData.U,
      Main3LargeAnalyticComplexCellCoverSelectionData.V,
      Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
      Main3LargeAnalyticComplexCellCoverSelectionData.rho,
      Main3LargeAnalyticComplexCellCoverSelectionData.z,
      Main3LargeAnalyticComplexCellCoverSelectionData.beta] using hend₀.1
  have hsqrt₀ : Real.sqrt K / 2 ≤ 1 / Q₀.mu := by
    simpa only [K, E, Delta] using Q₀.sqrt_K_div_two_le_reciprocal_mu
  have hS₀r₀ : S₀ ≤ 1 / Q₀.mu := by
    exact max_le hhalf₀ hsqrt₀
  have hrL₀ : 1 / Q₀.mu ≤ L := by
    have hupper : 1 / Q₀.mu ≤ Q₀.U + Q₀.V := by
      simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.mu,
        Main3LargeAnalyticComplexCellCoverSelectionData.U,
        Main3LargeAnalyticComplexCellCoverSelectionData.V,
        Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
        Main3LargeAnalyticComplexCellCoverSelectionData.rho,
        Main3LargeAnalyticComplexCellCoverSelectionData.z,
        Main3LargeAnalyticComplexCellCoverSelectionData.beta] using hend₀.2
    calc
      1 / Q₀.mu ≤ Q₀.U + Q₀.V := hupper
      _ = L := by
        dsimp only [Main3LargeAnalyticComplexCellCoverSelectionData.U,
          Main3LargeAnalyticComplexCellCoverSelectionData.V, L, K, E, Delta]
        norm_num
  have hradius₀ :=
    Q₀.cover_spec.complex_shortest_original_vector_norm_le_sqrt_div
      F ha Q₀.cert.R_pos hMreal (by norm_num : (0 : ℝ) < 1 / 2)
        Q₀.cert Q₀.ell_eq Q₀.rho_lower hhalf₀
  have hnorm₀ :=
    one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
      ha F Q₀.shortestVector Q₀.shortestVector_spec.1
  have hH₀ : 1 ≤ H₀ := by
    calc
      (1 : ℝ) ≤ ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding
            (shiftedSquareA h v) ha F.omega) Q₀.shortestVector‖ := hnorm₀
      _ ≤ Real.sqrt E / (1 / 2 : ℝ) := by
        simpa only [E, F,
          Main3LargeAnalyticComplexCellCoverSelectionData.shortestVector]
          using hradius₀
      _ = H₀ := by dsimp only [H₀]; ring
  have hS₀pos : 0 < S₀ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hSL : S₀ ≤ L := hS₀r₀.trans hrL₀
  have hAcoef : 0 ≤ Acoef := by
    have hlog : 0 ≤ Real.log H₀ := Real.log_nonneg hH₀
    dsimp only [Acoef]
    positivity
  have hBcoef : 0 ≤ Bcoef := by
    dsimp only [Bcoef]
    positivity
  have hSr : ∀ cell ∈ I, S₀ ≤ r cell := by
    intro cell hcell
    have hcell' : cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key := by simpa only [I] using hcell
    let c : ↑I := ⟨cell, hcell⟩
    let Q := main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha c
    have hend := Q.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
    have hlower : (1 / 2 : ℝ) ≤ 1 / Q.mu := by
      simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.mu,
        Main3LargeAnalyticComplexCellCoverSelectionData.U,
        Main3LargeAnalyticComplexCellCoverSelectionData.V,
        Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
        Main3LargeAnalyticComplexCellCoverSelectionData.rho,
        Main3LargeAnalyticComplexCellCoverSelectionData.z,
        Main3LargeAnalyticComplexCellCoverSelectionData.beta] using hend.1
    have hsqrt : Real.sqrt K / 2 ≤ 1 / Q.mu := by
      simpa only [K, E, Delta] using Q.sqrt_K_div_two_le_reciprocal_mu
    have hcutoff : S₀ ≤ 1 / Q.mu := max_le hlower hsqrt
    simpa only [r, main3LargeAnalytic_selectedComplexCellMu,
      dif_pos hcell', c, Q] using hcutoff
  have hrL : ∀ cell ∈ I, r cell ≤ L := by
    intro cell hcell
    have hcell' : cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key := by simpa only [I] using hcell
    let c : ↑I := ⟨cell, hcell⟩
    let Q := main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha c
    have hend := Q.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
    have hupper : 1 / Q.mu ≤ Q.U + Q.V := by
      simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.mu,
        Main3LargeAnalyticComplexCellCoverSelectionData.U,
        Main3LargeAnalyticComplexCellCoverSelectionData.V,
        Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
        Main3LargeAnalyticComplexCellCoverSelectionData.rho,
        Main3LargeAnalyticComplexCellCoverSelectionData.z,
        Main3LargeAnalyticComplexCellCoverSelectionData.beta] using hend.2
    calc
      r cell = 1 / Q.mu := by
        simp only [r, main3LargeAnalytic_selectedComplexCellMu,
          dif_pos hcell', c, Q]
      _ ≤ Q.U + Q.V := hupper
      _ = L := by
        dsimp only [Main3LargeAnalyticComplexCellCoverSelectionData.U,
          Main3LargeAnalyticComplexCellCoverSelectionData.V, L, K, E, Delta]
        norm_num
  have htail : ∀ T : ℝ, S₀ ≤ T →
      ((I.filter fun cell => T ≤ r cell).card : ℝ) ≤
        Acoef / T + Bcoef / T ^ 2 := by
    intro T hT
    have hhalfT : (1 / 2 : ℝ) ≤ T := (le_max_left _ _).trans hT
    have hband :=
      card_main3LargeAnalytic_complexCellReciprocalMinimumBand_le_weakTail
        htheta hY hi key ha (by simpa only [E] using hE)
          (by simpa only [E, H₀] using hH₀) T hhalfT
    simpa only [I, r, Acoef, Bcoef, E, Delta,
      main3LargeAnalytic_complexCellReciprocalMinimumBand] using hband
  have hsum := sum_le_linear_square_tail_completion
    I r S₀ L Acoef Bcoef hS₀pos hSL hAcoef hBcoef
      hSr hrL htail
  calc
    (∑ cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedComplexCellMu
        htheta hY hi key ha cell) = ∑ cell ∈ I, r cell := by rfl
    _ ≤ Acoef * (1 + Real.log (L / S₀)) +
        2 * Bcoef / S₀ := hsum

/-- Coarse manuscript-shaped form of the exact reciprocal-minimum sum: two
explicit logarithmic factors multiply the linear radial term, while the
quadratic lattice-area term has the square-root scale forced by the stronger
Minkowski cutoff. -/
theorem sum_main3LargeAnalytic_nonemptyComplexCell_reciprocalMinimum_le_intrinsicShape
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let K := (6 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
    let L := K / 2 + 2
    let H₀ := 2 * Real.sqrt E
    (∑ cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedComplexCellMu
        htheta hY hi key ha cell) ≤
      9216 * Real.sqrt E * (2 + Real.log H₀) *
          (1 + Real.log (2 * L)) +
        663552 * Real.sqrt
          (E * (main3UnbalancedM theta Y : ℝ) / Delta) := by
  dsimp only
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (6 * E / Mmesh) / Delta
  let S₀ := max (1 / 2 : ℝ) (Real.sqrt K / 2)
  let L := K / 2 + 2
  let H₀ := 2 * Real.sqrt E
  let Acoef := 9216 * Real.sqrt E * (2 + Real.log H₀)
  let Bcoef := 165888 * E / Delta
  have hsum :=
    sum_main3LargeAnalytic_nonemptyComplexCell_reciprocalMinimum_le
      htheta hY hi key ha hnonempty
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  let Q₀ := main3LargeAnalytic_complexCellCoverSelection
    htheta hY hi key ha c₀
  have hE : 0 < E := by simpa only [E] using Q₀.cert.R_pos
  have hMmesh : 0 < Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast (lt_of_lt_of_le (by omega)
      (six_le_main3UnbalancedM htheta hY))
  have hdiscZ : NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS₀pos : 0 < S₀ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hS₀half : (1 / 2 : ℝ) ≤ S₀ := le_max_left _ _
  have hS₀sqrt : Real.sqrt K / 2 ≤ S₀ := le_max_right _ _
  have hLpos : 0 < L := by dsimp only [L]; positivity
  have hratioPos : 0 < L / S₀ := div_pos hLpos hS₀pos
  have hratioUpper : L / S₀ ≤ 2 * L := by
    apply (div_le_iff₀ hS₀pos).2
    nlinarith
  have hlogUpper : Real.log (L / S₀) ≤ Real.log (2 * L) :=
    Real.log_le_log hratioPos hratioUpper
  have hend₀ := Q₀.cover_spec.reciprocal_firstSlopeSupNorm_mem_interval
  have hhalf₀ : (1 / 2 : ℝ) ≤ 1 / Q₀.mu := by
    simpa only [Main3LargeAnalyticComplexCellCoverSelectionData.mu,
      Main3LargeAnalyticComplexCellCoverSelectionData.U,
      Main3LargeAnalyticComplexCellCoverSelectionData.V,
      Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
      Main3LargeAnalyticComplexCellCoverSelectionData.rho,
      Main3LargeAnalyticComplexCellCoverSelectionData.z,
      Main3LargeAnalyticComplexCellCoverSelectionData.beta] using hend₀.1
  have hradius₀ :=
    Q₀.cover_spec.complex_shortest_original_vector_norm_le_sqrt_div
      F ha Q₀.cert.R_pos
        (by exact_mod_cast six_le_main3UnbalancedM htheta hY)
        (by norm_num : (0 : ℝ) < 1 / 2)
        Q₀.cert Q₀.ell_eq Q₀.rho_lower hhalf₀
  have hnorm₀ :=
    one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
      ha F Q₀.shortestVector Q₀.shortestVector_spec.1
  have hH₀ : 1 ≤ H₀ := by
    calc
      (1 : ℝ) ≤ ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding
            (shiftedSquareA h v) ha F.omega) Q₀.shortestVector‖ := hnorm₀
      _ ≤ Real.sqrt E / (1 / 2 : ℝ) := by
        simpa only [E, F,
          Main3LargeAnalyticComplexCellCoverSelectionData.shortestVector]
          using hradius₀
      _ = H₀ := by dsimp only [H₀]; ring
  have hAcoef : 0 ≤ Acoef := by
    have hlog : 0 ≤ Real.log H₀ := Real.log_nonneg hH₀
    dsimp only [Acoef]
    positivity
  have hlinear : Acoef * (1 + Real.log (L / S₀)) ≤
      Acoef * (1 + Real.log (2 * L)) := by
    gcongr
  have hinv : 1 / S₀ ≤ 2 / Real.sqrt K := by
    have hinv' := one_div_le_one_div_of_le
      (div_pos (Real.sqrt_pos.2 hK) (by norm_num)) hS₀sqrt
    simpa only [one_div_div] using hinv'
  have hBcoef : 0 ≤ Bcoef := by dsimp only [Bcoef]; positivity
  have harea : 2 * Bcoef / S₀ ≤
      663552 * Real.sqrt (E * Mmesh / Delta) := by
    have hscaled := div_sqrt_six_scaled_ratio_le_sqrt_product
      hE hMmesh hDelta
    have hKform : K = 6 * E / (Mmesh * Delta) := by
      dsimp only [K]
      ring
    calc
      2 * Bcoef / S₀ = 2 * Bcoef * (1 / S₀) := by ring
      _ ≤ 2 * Bcoef * (2 / Real.sqrt K) := by gcongr
      _ = 663552 * (E / Delta / Real.sqrt K) := by
        dsimp only [Bcoef]
        ring
      _ = 663552 *
          (E / Delta / Real.sqrt (6 * E / (Mmesh * Delta))) := by
        rw [hKform]
      _ ≤ 663552 * Real.sqrt (E * Mmesh / Delta) := by gcongr
  calc
    (∑ cell ∈ main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key,
      1 / main3LargeAnalytic_selectedComplexCellMu
        htheta hY hi key ha cell) ≤
        Acoef * (1 + Real.log (L / S₀)) + 2 * Bcoef / S₀ := by
      simpa only [E, Delta, Mmesh, K, S₀, L, H₀, Acoef, Bcoef] using hsum
    _ ≤ Acoef * (1 + Real.log (2 * L)) +
        663552 * Real.sqrt (E * Mmesh / Delta) :=
      add_le_add hlinear harea

end

end PellPaper
