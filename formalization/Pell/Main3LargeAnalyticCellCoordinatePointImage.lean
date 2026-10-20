import Pell.Main3LargeAnalyticBlockArchimedeanCellPartition
import Pell.GeneralBidegreeAuxiliaryRelation
import Pell.ShiftedSquareCoordinateSurfaceAdapter
import Pell.ShiftedSquareExplicitIntegralBasisHeight
import Mathlib.Tactic

/-!
# Integral homogeneous-point image of one main3 key-and-cell fibre

The determinant engine consumes integral homogeneous source/target pairs,
whereas the shifted-square block encoding retains the three auxiliary scalars
as well as the two primitive coordinate vectors.  On a fixed auxiliary-key
fibre those three scalars are constant, so forgetting them and retaining only
the two coordinate pairs remains injective.

This module makes that bridge literal.  It defines the no-reversal projection
to `GeneralBidegreeFormPoint`, maps one fixed auxiliary-key/archimedean-cell
point fibre through the deterministic block code, and proves exact
cardinality preservation together with preimage and same-certificate facts.
It makes no determinant estimate or point-count claim.
-/

namespace PellPaper

noncomputable section

/-- Forget the auxiliary scalars of a complete shifted-square code and retain
the source and target primitive coordinate pairs in the determinant engine's
literal order. -/
def shiftedSquareCoordinateCodePoint
    (C : ShiftedSquareCoordinateCode) : GeneralBidegreeFormPoint :=
  ((C.x 0, C.x 1), (C.y 0, C.y 1))

/-- The new projection is definitionally the no-reversal point convention
already frozen by the shifted-square surface adapter. -/
theorem shiftedSquareCoordinateCodePoint_eq_shiftedSquareCoordinatePoint
    (C : ShiftedSquareCoordinateCode) :
    shiftedSquareCoordinateCodePoint C =
      shiftedSquareCoordinatePoint C.x C.y := by
  rfl

/-- The three code scalars retained by an auxiliary key. -/
def shiftedSquareCoordinateCodeAuxiliaryTriple
    (C : ShiftedSquareCoordinateCode) : ℕ × ℕ × ℕ :=
  (C.C₀, C.r, C.ell)

/-- Forget `bζ` from an auxiliary key and retain the three scalars occurring
in a complete coordinate code. -/
def shiftedSquareAuxiliaryKeyCoordinateTriple
    (key : ShiftedSquareAuxiliaryKey) : ℕ × ℕ × ℕ :=
  (key.C₀, key.r, key.ell)

/-- The unique integral surface level determined by a fixed auxiliary key.
For keys arising from normalized packages, the denominator divides the
numerator by the exact coordinate factorization. -/
def shiftedSquareAuxiliaryKeySurfaceLevel
    (key : ShiftedSquareAuxiliaryKey) : ℤ :=
  ((key.C₀ : ℤ) ^ 2 * key.bζ) /
    ((key.r : ℤ) ^ 2 * (key.ell : ℤ))

/-- The exact nonzero surface value of a simultaneous normalized package is
the level determined solely by its four-field auxiliary key. -/
theorem
    ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceValue_eq_auxiliaryKeySurfaceLevel
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (shiftedSquareSurfaceForm P.t P.c P.y).eval (P.x 0) (P.x 1) =
        shiftedSquareAuxiliaryKeySurfaceLevel
          ⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ ∧
      shiftedSquareAuxiliaryKeySurfaceLevel
          ⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ ≠ 0 := by
  let denom : ℤ := (P.r : ℤ) ^ 2 * (P.ell : ℤ)
  let numerator : ℤ := (P.minkowski.C₀ : ℤ) ^ 2 * P.bζ
  let value : ℤ :=
    (shiftedSquareSurfaceForm P.t P.c P.y).eval (P.x 0) (P.x 1)
  have hr0 : (P.r : ℤ) ≠ 0 := by
    exact_mod_cast P.r_pos.ne'
  have hell0 : (P.ell : ℤ) ≠ 0 := by
    exact_mod_cast P.ell_pos.ne'
  have hdenom0 : denom ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 hr0) hell0
  have hmul : denom * value = numerator := by
    simpa only [denom, value, numerator] using P.special_surface_relation
  have hdiv : denom ∣ numerator := ⟨value, hmul.symm⟩
  have hquotientMul : numerator / denom * denom = numerator :=
    Int.ediv_mul_cancel hdiv
  have hvalue : value = numerator / denom := by
    apply mul_right_cancel₀ hdenom0
    calc
      value * denom = denom * value := mul_comm _ _
      _ = numerator := hmul
      _ = numerator / denom * denom := hquotientMul.symm
  have hlevel :
      value = shiftedSquareAuxiliaryKeySurfaceLevel
        ⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ := by
    simpa only [shiftedSquareAuxiliaryKeySurfaceLevel, denom, numerator] using
      hvalue
  refine ⟨hlevel, ?_⟩
  rw [← hlevel]
  exact P.special_surface_level_ne_zero

/-- Two complete codes are equal once their three auxiliary scalars and their
four displayed homogeneous coordinates agree. -/
theorem shiftedSquareCoordinateCode_eq_of_auxiliaryTriple_eq_of_point_eq
    {C C' : ShiftedSquareCoordinateCode}
    (haux : shiftedSquareCoordinateCodeAuxiliaryTriple C =
      shiftedSquareCoordinateCodeAuxiliaryTriple C')
    (hpoint : shiftedSquareCoordinateCodePoint C =
      shiftedSquareCoordinateCodePoint C') :
    C = C' := by
  have hC₀ : C.C₀ = C'.C₀ := by
    simpa only [shiftedSquareCoordinateCodeAuxiliaryTriple] using
      congrArg (fun q : ℕ × ℕ × ℕ => q.1) haux
  have hr : C.r = C'.r := by
    simpa only [shiftedSquareCoordinateCodeAuxiliaryTriple] using
      congrArg (fun q : ℕ × ℕ × ℕ => q.2.1) haux
  have hell : C.ell = C'.ell := by
    simpa only [shiftedSquareCoordinateCodeAuxiliaryTriple] using
      congrArg (fun q : ℕ × ℕ × ℕ => q.2.2) haux
  have hx0 : C.x 0 = C'.x 0 := by
    simpa only [shiftedSquareCoordinateCodePoint] using
      congrArg (fun q : GeneralBidegreeFormPoint => q.1.1) hpoint
  have hx1 : C.x 1 = C'.x 1 := by
    simpa only [shiftedSquareCoordinateCodePoint] using
      congrArg (fun q : GeneralBidegreeFormPoint => q.1.2) hpoint
  have hy0 : C.y 0 = C'.y 0 := by
    simpa only [shiftedSquareCoordinateCodePoint] using
      congrArg (fun q : GeneralBidegreeFormPoint => q.2.1) hpoint
  have hy1 : C.y 1 = C'.y 1 := by
    simpa only [shiftedSquareCoordinateCodePoint] using
      congrArg (fun q : GeneralBidegreeFormPoint => q.2.2) hpoint
  have hx : C.x = C'.x := by
    funext j
    fin_cases j
    · exact hx0
    · exact hx1
  have hy : C.y = C'.y := by
    funext j
    fin_cases j
    · exact hy0
    · exact hy1
  cases C
  cases C'
  simp_all

/-- Recover a `Fin 2` source vector from an integral homogeneous point. -/
def shiftedSquareCoordinatePointSourceVector
    (z : GeneralBidegreeFormPoint) : Fin 2 → ℤ :=
  ![z.1.1, z.1.2]

/-- Recover a `Fin 2` target vector from an integral homogeneous point. -/
def shiftedSquareCoordinatePointTargetVector
    (z : GeneralBidegreeFormPoint) : Fin 2 → ℤ :=
  ![z.2.1, z.2.2]

@[simp]
theorem shiftedSquareCoordinatePointSourceVector_codePoint
    (C : ShiftedSquareCoordinateCode) :
    shiftedSquareCoordinatePointSourceVector
      (shiftedSquareCoordinateCodePoint C) = C.x := by
  funext j
  fin_cases j <;> rfl

@[simp]
theorem shiftedSquareCoordinatePointTargetVector_codePoint
    (C : ShiftedSquareCoordinateCode) :
    shiftedSquareCoordinatePointTargetVector
      (shiftedSquareCoordinateCodePoint C) = C.y := by
  funext j
  fin_cases j <;> rfl

/-- At every attached block point, the first three fields of the deterministic
complete code are exactly the first three fields of its deterministic
auxiliary key. -/
theorem main3LargeAnalytic_blockCoordinateCode_auxiliaryTriple
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    shiftedSquareCoordinateCodeAuxiliaryTriple
        (main3LargeAnalytic_blockCoordinateCode htheta hY hi p) =
      shiftedSquareAuxiliaryKeyCoordinateTriple
        (main3LargeAnalytic_blockAuxiliaryKey htheta hY hi p) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY hi p
  change shiftedSquareCoordinateCodeAuxiliaryTriple C.encoded.code =
    shiftedSquareAuxiliaryKeyCoordinateTriple
      ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩
  rw [C.encoded_code_eq]
  rfl

private theorem main3LargeAnalytic_cellCoordinate_eight_le
    {Y : ℕ} (hY : 65536 ≤ Y) : 8 ≤ Y := by
  omega

/-- The common quadratic-linear surface coefficients for one fixed block.
The explicit integral basis is chosen from the fixed shift and active index,
before any point in the block is selected. -/
noncomputable def main3LargeAnalytic_blockCoordinateSurfaceCoefficients
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Fin 3 → Fin 2 → ℤ := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  exact shiftedSquareSurfaceCoefficients B.t B.c

/-- Every coefficient of the fixed block surface has the canonical uniform
height bound depending only on the fixed shift. -/
theorem main3LargeAnalytic_blockCoordinateSurfaceCoefficients_abs_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (i : Fin 3) (j : Fin 2) :
    |main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i j| ≤
      ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℤ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  change |shiftedSquareSurfaceCoefficients B.t B.c i j| ≤ _
  calc
    |shiftedSquareSurfaceCoefficients B.t B.c i j| ≤
        (shiftedSquareSurfaceCoefficientHeight B.c : ℤ) :=
      abs_shiftedSquareSurfaceCoefficients_le_height
        B.t B.c B.t_zero_or_one i j
    _ ≤ ((8 * (shiftedSquareA h v).natAbs + 4 : ℕ) : ℤ) := by
      exact_mod_cast
        shiftedSquareSurfaceCoefficientHeight_le_eight_mul_natAbs_add_four
          B.basis B.omega B.t B.c B.basis_zero B.basis_one
            B.t_zero_or_one B.omega_sq

/-- Evaluate the fixed block surface on a literal determinant-engine point. -/
noncomputable def main3LargeAnalytic_blockCoordinateSurfaceEval
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (z : GeneralBidegreeFormPoint) : ℤ :=
  quadraticLinearFormEval
    (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
    (shiftedSquareCoordinatePointSourceVector z)
    (shiftedSquareCoordinatePointTargetVector z)

/-- The integral homogeneous point attached to a block point by forgetting
only the three auxiliary scalars from its deterministic complete code. -/
noncomputable def main3LargeAnalytic_blockCellCoordinatePoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    GeneralBidegreeFormPoint :=
  shiftedSquareCoordinateCodePoint
    (main3LargeAnalytic_blockCoordinateCode htheta
      (main3LargeAnalytic_cellCoordinate_eight_le hY) hi p)

/-- On one fixed auxiliary-key/archimedean-cell fibre, the integral
homogeneous-point projection is injective.  Equality of point coordinates and
equality of the fixed key reconstruct the complete code, after which the
block-code injection recovers the attached point. -/
theorem main3LargeAnalytic_blockCellCoordinatePoint_injOn
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex) :
    Set.InjOn
      (main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi)
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell) := by
  intro p hp q hq hpoint
  let hY8 : 8 ≤ Y := main3LargeAnalytic_cellCoordinate_eight_le hY
  have hpKey :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_iff
      htheta hY hi).mp hp |>.1
  have hqKey :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_iff
      htheta hY hi).mp hq |>.1
  have hpAux :=
    main3LargeAnalytic_blockCoordinateCode_auxiliaryTriple
      htheta hY8 hi p
  have hqAux :=
    main3LargeAnalytic_blockCoordinateCode_auxiliaryTriple
      htheta hY8 hi q
  have haux :
      shiftedSquareCoordinateCodeAuxiliaryTriple
          (main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p) =
        shiftedSquareCoordinateCodeAuxiliaryTriple
          (main3LargeAnalytic_blockCoordinateCode htheta hY8 hi q) := by
    calc
      _ = shiftedSquareAuxiliaryKeyCoordinateTriple
            (main3LargeAnalytic_blockAuxiliaryKey htheta hY8 hi p) := hpAux
      _ = shiftedSquareAuxiliaryKeyCoordinateTriple key := by rw [hpKey]
      _ = shiftedSquareAuxiliaryKeyCoordinateTriple
            (main3LargeAnalytic_blockAuxiliaryKey htheta hY8 hi q) := by
          rw [hqKey]
      _ = _ := hqAux.symm
  have hcode :
      main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p =
        main3LargeAnalytic_blockCoordinateCode htheta hY8 hi q :=
    shiftedSquareCoordinateCode_eq_of_auxiliaryTriple_eq_of_point_eq
      haux hpoint
  exact main3LargeAnalytic_blockCoordinateCode_injective
    htheta hY8 hi hcode

/-- The literal finite family of integral homogeneous points arising from one
fixed auxiliary-key/archimedean-cell point fibre. -/
noncomputable def
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex) :
    Finset GeneralBidegreeFormPoint :=
  (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
    htheta hY hi key cell).image
      (main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi)

/-- Image membership is witnessed by an attached point in the exact same
fixed key-and-cell fibre. -/
@[simp]
theorem mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_iff
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint} :
    z ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell ↔
      ∃ p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key cell,
        main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi p = z := by
  simp [main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage]

/-- Every image point has a unique preimage in its fixed key-and-cell fibre. -/
theorem existsUnique_main3LargeAnalytic_blockCellCoordinatePoint_preimage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    ∃! p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N,
      p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key cell ∧
        main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi p = z := by
  obtain ⟨p, hp, hpz⟩ :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_iff
      htheta hY hi).mp hz
  refine ⟨p, ⟨hp, hpz⟩, ?_⟩
  intro q hq
  exact main3LargeAnalytic_blockCellCoordinatePoint_injOn
    htheta hY hi key cell hq.1 hp (hq.2.trans hpz.symm)

/-- Passing from one fixed key-and-cell point fibre to its literal integral
homogeneous-point image preserves cardinality exactly. -/
theorem card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_eq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).card =
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell).card := by
  exact Finset.card_image_of_injOn
    (main3LargeAnalytic_blockCellCoordinatePoint_injOn
      htheta hY hi key cell)

/-- Image membership retains the exact deterministic certificate: its four
auxiliary scalars give the fixed key, its package has the selected-cell
geometry, its encoded code is the block code, and the displayed image point
is literally the `x`/`y` pair of that same package. -/
theorem main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    ∃ p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell,
      letI : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
        ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
      let hY8 : 8 ≤ Y := main3LargeAnalytic_cellCoordinate_eight_le hY
      let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
        htheta hY8 hi p
      (⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩ :
          ShiftedSquareAuxiliaryKey) = key ∧
        main3LargeAnalytic_blockPointArchimedeanCellSelector
            htheta hY hi p = cell ∧
          InMain3LargeAnalyticArchimedeanCell
              (main3UnbalancedM theta Y) C.P cell ∧
            main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p =
                C.encoded.code ∧
              z = ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := by
  obtain ⟨p, hp, hpz⟩ :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_iff
      htheta hY hi).mp hz
  refine ⟨p, hp, ?_⟩
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := main3LargeAnalytic_cellCoordinate_eight_le hY
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  have hpSpec :=
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_spec
      htheta hY hi hp
  have hsame :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_sameCertificate
      htheta hY hi p
  have hkey :
      (⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩ :
        ShiftedSquareAuxiliaryKey) = key := by
    change main3LargeAnalytic_blockAuxiliaryKey htheta hY8 hi p = key
    exact hpSpec.1
  have hgeometry : InMain3LargeAnalyticArchimedeanCell
      (main3UnbalancedM theta Y) C.P cell := by
    rw [← hpSpec.2.1]
    exact hsame.1
  have hzPackage :
      z = ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := by
    calc
      z = main3LargeAnalytic_blockCellCoordinatePoint
          htheta hY hi p := hpz.symm
      _ = shiftedSquareCoordinateCodePoint
          (main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p) := rfl
      _ = shiftedSquareCoordinateCodePoint C.encoded.code := by rw [hsame.2]
      _ = ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := by
        rw [C.encoded_code_eq]
        rfl
  exact ⟨hkey, hpSpec.2.1, hgeometry, hsame.2, hzPackage⟩

/-- Both homogeneous coordinate pairs of every image point are primitive,
as they are literally the `x` and `y` vectors of the retained package. -/
theorem main3LargeAnalytic_blockCellCoordinatePointImage_primitive
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    IsCoprime z.1.1 z.1.2 ∧ IsCoprime z.2.1 z.2.2 := by
  obtain ⟨p, _hp, hpz⟩ :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_iff
      htheta hY hi).mp hz
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := main3LargeAnalytic_cellCoordinate_eight_le hY
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  have hcode :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_sameCertificate
      htheta hY hi p |>.2
  have hzPackage :
      z = ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := by
    calc
      z = main3LargeAnalytic_blockCellCoordinatePoint
          htheta hY hi p := hpz.symm
      _ = shiftedSquareCoordinateCodePoint
          (main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p) := rfl
      _ = shiftedSquareCoordinateCodePoint C.encoded.code := by rw [hcode]
      _ = ((C.P.x 0, C.P.x 1), (C.P.y 0, C.P.y 1)) := by
        rw [C.encoded_code_eq]
        rfl
  rw [hzPackage]
  exact ⟨C.P.x_primitive, C.P.y_primitive⟩

/-- Every integral homogeneous point in the fixed key-and-cell image lies on
the block's one fixed quadratic-linear coordinate surface at the one fixed
nonzero level determined by `key`. -/
theorem main3LargeAnalytic_blockCellCoordinatePointImage_surfaceData
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    main3LargeAnalytic_blockCoordinateSurfaceEval hi z =
        shiftedSquareAuxiliaryKeySurfaceLevel key ∧
      shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 := by
  obtain ⟨p, hp, hpz⟩ :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_iff
      htheta hY hi).mp hz
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := main3LargeAnalytic_cellCoordinate_eight_le hY
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  have hpSpec :=
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_spec
      htheta hY hi hp
  have hsame :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_sameCertificate
      htheta hY hi p
  have hkey :
      (⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩ :
        ShiftedSquareAuxiliaryKey) = key := by
    change main3LargeAnalytic_blockAuxiliaryKey htheta hY8 hi p = key
    exact hpSpec.1
  have hsurface := C.P.surfaceValue_eq_auxiliaryKeySurfaceLevel
  have hsurfaceValue :
      (shiftedSquareSurfaceForm C.P.t C.P.c C.P.y).eval
          (C.P.x 0) (C.P.x 1) =
        shiftedSquareAuxiliaryKeySurfaceLevel key := by
    rw [← hkey]
    exact hsurface.1
  have hlevel0 : shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 := by
    rw [← hkey]
    exact hsurface.2
  refine ⟨?_, hlevel0⟩
  rw [← hpz]
  change quadraticLinearFormEval
      (shiftedSquareSurfaceCoefficients B.t B.c)
      (shiftedSquareCoordinatePointSourceVector
        (shiftedSquareCoordinateCodePoint
          (main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p)))
      (shiftedSquareCoordinatePointTargetVector
        (shiftedSquareCoordinateCodePoint
          (main3LargeAnalytic_blockCoordinateCode htheta hY8 hi p))) = _
  rw [hsame.2, C.encoded_code_eq,
    shiftedSquareCoordinatePointSourceVector_codePoint,
    shiftedSquareCoordinatePointTargetVector_codePoint]
  rw [← C.t_eq, ← C.c_eq]
  exact
    (quadraticLinearFormEval_shiftedSquareSurfaceCoefficients
      C.P.t C.P.c C.P.x C.P.y).trans hsurfaceValue

end

end PellPaper
