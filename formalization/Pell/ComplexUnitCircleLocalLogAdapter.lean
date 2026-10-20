import Pell.ComplexUnitCircleSquareMapCellPairCover
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# Local logarithms on complex unit-circle square-map cells

The complex-place determinant route needs additive coordinates near a fixed
unit-circle source centre.  This module uses the principal complex logarithm
only inside the radius-`1/2` ball about `1`, where Mathlib's explicit
`3/2`-Lipschitz bound applies.

For one accepted square-map cell, a source point is written relative to an
arbitrary unit source centre in that cell, while the target is written
relative to the square of that centre.  A separate defect logarithm retains
the finer pointwise target-versus-source-square error.  No branch-additivity,
Taylor determinant estimate, determinant decay, or point count is asserted.
-/

namespace PellPaper

noncomputable section

/-- The principal local logarithm of `z` relative to the nonzero centre `c`. -/
def complexUnitCircleLocalLog (z c : ℂ) : ℂ :=
  Complex.log (z / c)

/-- For unit `z,c` within chordal distance `1/2`, the principal local
logarithm exponentiates to the exact quotient and has the explicit
`3/2`-Lipschitz norm bound. -/
theorem complexUnitCircleLocalLog_spec
    {z c : ℂ} (hzNorm : ‖z‖ = 1) (hcNorm : ‖c‖ = 1)
    (hclose : ‖z - c‖ ≤ 1 / 2) :
    Complex.exp (complexUnitCircleLocalLog z c) = z / c ∧
      ‖complexUnitCircleLocalLog z c‖ ≤ (3 / 2) * ‖z - c‖ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcNorm]; norm_num)
  have hquotient : z / c = 1 + (z - c) / c := by
    field_simp [hc0]
    ring
  constructor
  · exact Complex.exp_log (div_ne_zero hz0 hc0)
  · rw [complexUnitCircleLocalLog, hquotient]
    have hsmall : ‖(z - c) / c‖ ≤ 1 / 2 := by
      simpa only [norm_div, hcNorm, div_one] using hclose
    simpa only [norm_div, hcNorm, div_one] using
      Complex.norm_log_one_add_half_le_self hsmall

/-- The local logarithm of a quotient of two unit complex numbers is purely
imaginary.  This records the angular meaning of the local coordinate without
choosing or comparing arguments. -/
theorem complexUnitCircleLocalLog_re_eq_zero
    {z c : ℂ} (hzNorm : ‖z‖ = 1) (hcNorm : ‖c‖ = 1) :
    (complexUnitCircleLocalLog z c).re = 0 := by
  rw [complexUnitCircleLocalLog, Complex.log_re, norm_div, hzNorm, hcNorm]
  norm_num

/-- The square-map defect logarithm is the principal local logarithm of the
target relative to the exact source square. -/
def complexUnitCircleSquareMapDefectLog (z w : ℂ) : ℂ :=
  complexUnitCircleLocalLog w (z ^ 2)

/-- A pointwise unit-circle square-map error at most `epsilon ≤ 1/2` has an
exact logarithmic defect bounded by `(3/2) epsilon`. -/
theorem complexUnitCircleSquareMapDefectLog_spec
    {z w : ℂ} (hzNorm : ‖z‖ = 1) (hwNorm : ‖w‖ = 1)
    {epsilon : ℝ} (herror : ‖w - z ^ 2‖ ≤ epsilon)
    (hepsilon : epsilon ≤ 1 / 2) :
    Complex.exp (complexUnitCircleSquareMapDefectLog z w) = w / z ^ 2 ∧
      ‖complexUnitCircleSquareMapDefectLog z w‖ ≤ (3 / 2) * epsilon := by
  have hzSqNorm : ‖z ^ 2‖ = 1 := by rw [norm_pow, hzNorm]; norm_num
  have hclose : ‖w - z ^ 2‖ ≤ 1 / 2 := herror.trans hepsilon
  have hspec := complexUnitCircleLocalLog_spec hwNorm hzSqNorm hclose
  exact ⟨hspec.1, hspec.2.trans
    (mul_le_mul_of_nonneg_left herror (by norm_num))⟩

/-- The source logarithmic coordinate relative to a chosen unit source
centre. -/
def complexUnitCircleSourceLocalLog (z centre : ℂ) : ℂ :=
  complexUnitCircleLocalLog z centre

/-- The target logarithmic coordinate relative to the square of a chosen
unit source centre.  This is the literal "twice the source centre"
normalization. -/
def complexUnitCircleTargetLocalLog (w centre : ℂ) : ℂ :=
  complexUnitCircleLocalLog w (centre ^ 2)

private theorem two_div_natCast_le_half
    {M : ℕ} (hM : 4 ≤ M) : 2 / (M : ℝ) ≤ 1 / 2 := by
  have hMreal : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by positivity
  apply (div_le_iff₀ hMpos).2
  nlinarith

private theorem one_div_natCast_le_half
    {M : ℕ} (hM : 2 ≤ M) : 1 / (M : ℝ) ≤ 1 / 2 := by
  have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by positivity
  apply (div_le_iff₀ hMpos).2
  nlinarith

private theorem five_div_natCast_le_half
    {M : ℕ} (hM : 10 ≤ M) : 5 / (M : ℝ) ≤ 1 / 2 := by
  have hMreal : (10 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by positivity
  apply (div_le_iff₀ hMpos).2
  nlinarith

/-- Relative to any other source point in the same accepted slope cell, the
source local logarithm has norm at most `3/M`. -/
theorem complexUnitCircleSlopeCell_sourceLocalLog_spec
    {M : ℕ} (hM : 4 ≤ M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {z centre : ℂ}
    (hz : InComplexUnitCircleSlopeCell M i z)
    (hcentre : InComplexUnitCircleSlopeCell M i centre) :
    Complex.exp (complexUnitCircleSourceLocalLog z centre) = z / centre ∧
      ‖complexUnitCircleSourceLocalLog z centre‖ ≤ 3 / (M : ℝ) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hdist : ‖z - centre‖ ≤ 2 / (M : ℝ) :=
    norm_sub_le_two_div_of_mem_complexUnitCircleSlopeCell
      hMpos hi hz hcentre
  have hclose : ‖z - centre‖ ≤ 1 / 2 :=
    hdist.trans (two_div_natCast_le_half hM)
  have hspec := complexUnitCircleLocalLog_spec hz.1 hcentre.1 hclose
  refine ⟨hspec.1, hspec.2.trans ?_⟩
  calc
    (3 / 2) * ‖z - centre‖ ≤ (3 / 2) * (2 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = 3 / (M : ℝ) := by ring

/-- A target in the accepted tube, measured from the square of any source
centre in the associated slope cell, has local logarithm at most
`15/(2M)`. -/
theorem complexUnitCircleSquareTargetTube_targetLocalLog_spec
    {M : ℕ} (hM : 10 ≤ M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {w centre : ℂ}
    (hw : InComplexUnitCircleSquareTargetTube M i w)
    (hcentre : InComplexUnitCircleSlopeCell M i centre) :
    Complex.exp (complexUnitCircleTargetLocalLog w centre) =
        w / centre ^ 2 ∧
      ‖complexUnitCircleTargetLocalLog w centre‖ ≤
        15 / (2 * (M : ℝ)) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hdist : ‖w - centre ^ 2‖ ≤ 5 / (M : ℝ) :=
    norm_target_sub_source_sq_le_five_div_of_mem
      hMpos hi hcentre hw
  have hclose : ‖w - centre ^ 2‖ ≤ 1 / 2 :=
    hdist.trans (five_div_natCast_le_half hM)
  have hcentreSqNorm : ‖centre ^ 2‖ = 1 := by
    rw [norm_pow, hcentre.1]
    norm_num
  have hspec := complexUnitCircleLocalLog_spec hw.1 hcentreSqNorm hclose
  refine ⟨hspec.1, hspec.2.trans ?_⟩
  calc
    (3 / 2) * ‖w - centre ^ 2‖ ≤
        (3 / 2) * (5 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = 15 / (2 * (M : ℝ)) := by ring

/-- The accepted cell predicate alone gives a `15/(2M)` defect logarithm.
The next theorem retains any finer pointwise square-map error instead. -/
theorem complexUnitCircleSquareMapCellPair_defectLog_spec
    {M : ℕ} (hM : 10 ≤ M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {z w : ℂ}
    (hp : InComplexUnitCircleSquareMapCellPair M i (z, w)) :
    Complex.exp (complexUnitCircleSquareMapDefectLog z w) = w / z ^ 2 ∧
      ‖complexUnitCircleSquareMapDefectLog z w‖ ≤
        15 / (2 * (M : ℝ)) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have herror : ‖w - z ^ 2‖ ≤ 5 / (M : ℝ) :=
    norm_target_sub_source_sq_le_five_div_of_mem hMpos hi hp.1 hp.2
  have hspec := complexUnitCircleSquareMapDefectLog_spec
    hp.1.1 hp.2.1 herror (five_div_natCast_le_half hM)
  refine ⟨hspec.1, hspec.2.trans_eq ?_⟩
  ring

/-- If the point entered its cell with a finer target-versus-own-source-square
error `epsilon`, the defect logarithm retains the smaller
`(3/2) epsilon` scale rather than degrading it to the cell width. -/
theorem complexUnitCircleSquareMapCellPair_defectLog_spec_of_pointwiseError
    {M : ℕ} {i : ComplexUnitCircleSlopeCellIndex} {z w : ℂ}
    (hp : InComplexUnitCircleSquareMapCellPair M i (z, w))
    {epsilon : ℝ} (herror : ‖w - z ^ 2‖ ≤ epsilon)
    (hepsilon : epsilon ≤ 1 / 2) :
    Complex.exp (complexUnitCircleSquareMapDefectLog z w) = w / z ^ 2 ∧
      ‖complexUnitCircleSquareMapDefectLog z w‖ ≤ (3 / 2) * epsilon := by
  exact complexUnitCircleSquareMapDefectLog_spec
    hp.1.1 hp.2.1 herror hepsilon

/-- In the common case where the own-pair square-map error is at most the
mesh width, the defect logarithm has the sharper bound `3/(2M)`.  This uses
an explicit own-pair hypothesis; target-tube membership alone only gives
`15/(2M)`. -/
theorem complexUnitCircleSquareMapCellPair_defectLog_spec_of_meshError
    {M : ℕ} (hM : 2 ≤ M) {i : ComplexUnitCircleSlopeCellIndex}
    {z w : ℂ} (hp : InComplexUnitCircleSquareMapCellPair M i (z, w))
    (herror : ‖w - z ^ 2‖ ≤ 1 / (M : ℝ)) :
    Complex.exp (complexUnitCircleSquareMapDefectLog z w) = w / z ^ 2 ∧
      ‖complexUnitCircleSquareMapDefectLog z w‖ ≤
        3 / (2 * (M : ℝ)) := by
  have hspec := complexUnitCircleSquareMapDefectLog_spec
    hp.1.1 hp.2.1 herror (one_div_natCast_le_half hM)
  refine ⟨hspec.1, hspec.2.trans_eq ?_⟩
  ring

/-- Exact multiplicative parametrization by the source and defect local
logs.  It avoids any false global claim that the principal logarithm is
additive: only its exponential is used. -/
theorem complexUnitCircleLocalLogs_exactSquareMapParametrization
    {z w centre : ℂ} (hzNorm : ‖z‖ = 1) (hwNorm : ‖w‖ = 1)
    (hcentreNorm : ‖centre‖ = 1) :
    centre * Complex.exp (complexUnitCircleSourceLocalLog z centre) = z ∧
      centre ^ 2 * Complex.exp
          (2 * complexUnitCircleSourceLocalLog z centre +
            complexUnitCircleSquareMapDefectLog z w) = w ∧
        Complex.exp (complexUnitCircleTargetLocalLog w centre) =
          Complex.exp (2 * complexUnitCircleSourceLocalLog z centre +
            complexUnitCircleSquareMapDefectLog z w) := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hwNorm]; norm_num)
  have hcentre0 : centre ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hcentreNorm]; norm_num)
  have hsourceExp :
      Complex.exp (complexUnitCircleSourceLocalLog z centre) = z / centre := by
    exact Complex.exp_log (div_ne_zero hz0 hcentre0)
  have htargetExp :
      Complex.exp (complexUnitCircleTargetLocalLog w centre) =
        w / centre ^ 2 := by
    exact Complex.exp_log (div_ne_zero hw0 (pow_ne_zero 2 hcentre0))
  have hdefectExp :
      Complex.exp (complexUnitCircleSquareMapDefectLog z w) = w / z ^ 2 := by
    exact Complex.exp_log (div_ne_zero hw0 (pow_ne_zero 2 hz0))
  have hsourceTwoExp :
      Complex.exp (2 * complexUnitCircleSourceLocalLog z centre) =
        Complex.exp (complexUnitCircleSourceLocalLog z centre) ^ 2 := by
    simpa using
      (Complex.exp_nat_mul (complexUnitCircleSourceLocalLog z centre) 2)
  constructor
  · rw [hsourceExp]
    field_simp [hcentre0]
  constructor
  · rw [Complex.exp_add, hsourceTwoExp, hsourceExp, hdefectExp]
    field_simp [hz0, hcentre0]
  · rw [htargetExp, Complex.exp_add, hsourceTwoExp, hsourceExp, hdefectExp]
    field_simp [hz0, hcentre0]

/-- Full local-log package supplied by one accepted complex square-map cell.
The source is `O(1/M)`, the target is centred at the square of the source
centre and is `O(1/M)`, and the defect keeps an explicitly supplied smaller
pointwise error `epsilon`. -/
theorem complexUnitCircleSquareMapCellPair_localLogCoordinates
    {M : ℕ} (hM : 10 ≤ M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    {z w centre : ℂ}
    (hp : InComplexUnitCircleSquareMapCellPair M i (z, w))
    (hcentre : InComplexUnitCircleSlopeCell M i centre)
    {epsilon : ℝ} (herror : ‖w - z ^ 2‖ ≤ epsilon)
    (hepsilonMesh : epsilon ≤ 1 / (M : ℝ)) :
    let alpha := complexUnitCircleSourceLocalLog z centre
    let beta := complexUnitCircleTargetLocalLog w centre
    let delta := complexUnitCircleSquareMapDefectLog z w
    (Complex.exp alpha = z / centre ∧ ‖alpha‖ ≤ 3 / (M : ℝ)) ∧
      (Complex.exp beta = w / centre ^ 2 ∧
        ‖beta‖ ≤ 15 / (2 * (M : ℝ))) ∧
      (Complex.exp delta = w / z ^ 2 ∧
        ‖delta‖ ≤ (3 / 2) * epsilon ∧
        ‖delta‖ ≤ 3 / (2 * (M : ℝ))) ∧
      centre * Complex.exp alpha = z ∧
      centre ^ 2 * Complex.exp (2 * alpha + delta) = w ∧
      Complex.exp beta = Complex.exp (2 * alpha + delta) := by
  dsimp only
  have hsource := complexUnitCircleSlopeCell_sourceLocalLog_spec
    (hM.trans' (by norm_num)) hi hp.1 hcentre
  have htarget := complexUnitCircleSquareTargetTube_targetLocalLog_spec
    hM hi hp.2 hcentre
  have hepsilonHalf : epsilon ≤ 1 / 2 :=
    hepsilonMesh.trans
      (one_div_natCast_le_half (hM.trans' (by norm_num)))
  have hdefect :=
    complexUnitCircleSquareMapCellPair_defectLog_spec_of_pointwiseError
      hp herror hepsilonHalf
  have hdefectMesh :
      ‖complexUnitCircleSquareMapDefectLog z w‖ ≤
        3 / (2 * (M : ℝ)) := by
    calc
      ‖complexUnitCircleSquareMapDefectLog z w‖ ≤
          (3 / 2) * epsilon := hdefect.2
      _ ≤ (3 / 2) * (1 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hepsilonMesh (by norm_num)
      _ = 3 / (2 * (M : ℝ)) := by ring
  have hexact := complexUnitCircleLocalLogs_exactSquareMapParametrization
    hp.1.1 hp.2.1 hcentre.1
  exact ⟨hsource, htarget, ⟨hdefect.1, hdefect.2, hdefectMesh⟩, hexact⟩

/-- Project specialization: a shifted-square localization certificate keeps
its original `8*sqrt |a|/n` error in the defect coordinate after the ratios
have entered an accepted complex square-map cell.  Thus the target is centred
at twice the source centre without replacing the arithmetic error by `1/M`. -/
theorem shiftedSquare_complexUnitCircleSquareMapCellPair_localLogCoordinates
    {a : ℤ} {d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hM : 10 ≤ M)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (L : ShiftedSquareEmbeddingRatioLocalizationCertificate heq P sigma)
    {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    (hcell : InComplexUnitCircleSquareMapCellPair M i
      (shiftedSquareSourceEmbeddingRatio P sigma,
        shiftedSquareTargetEmbeddingRatio P sigma))
    {centre : ℂ}
    (hcentre : InComplexUnitCircleSlopeCell M i centre)
    (hmesh : (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) ≤
      1 / (M : ℝ)) :
    let z := shiftedSquareSourceEmbeddingRatio P sigma
    let target := shiftedSquareTargetEmbeddingRatio P sigma
    let alpha := complexUnitCircleSourceLocalLog z centre
    let beta := complexUnitCircleTargetLocalLog target centre
    let delta := complexUnitCircleSquareMapDefectLog z target
    (Complex.exp alpha = z / centre ∧ ‖alpha‖ ≤ 3 / (M : ℝ)) ∧
      (Complex.exp beta = target / centre ^ 2 ∧
        ‖beta‖ ≤ 15 / (2 * (M : ℝ))) ∧
      (Complex.exp delta = target / z ^ 2 ∧
        ‖delta‖ ≤ (3 / 2) *
          ((8 * Real.sqrt |(a : ℝ)|) / (n : ℝ)) ∧
        ‖delta‖ ≤ 3 / (2 * (M : ℝ))) ∧
      centre * Complex.exp alpha = z ∧
      centre ^ 2 * Complex.exp (2 * alpha + delta) = target ∧
      Complex.exp beta = Complex.exp (2 * alpha + delta) := by
  dsimp only
  have herror :
      ‖shiftedSquareTargetEmbeddingRatio P sigma -
          shiftedSquareSourceEmbeddingRatio P sigma ^ 2‖ ≤
        (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) :=
    norm_target_sub_source_sq_le_of_unit_quotientError
      hcell.1.1 L.quotient_error
  exact complexUnitCircleSquareMapCellPair_localLogCoordinates
    hM hi hcell hcentre herror hmesh

end

end PellPaper
