import Pell.Main3LargeAnalyticScaledCoordinatePackage
import Pell.ShiftedSquareFixedBasisNormalizedCoordinates
import Pell.ShiftedSquareAuxiliaryParameterBounds
import Pell.ShiftedSquareCoordinateEncoding
import Mathlib.Tactic

/-!
# Fixed-basis encoded points on main3 large-analytic blocks

For a fixed large-analytic block, the quadratic shift is fixed.  This module
chooses one explicit integral basis from that shift before a block point is
introduced, constructs every point's simultaneous normalized coordinates in
that basis, and bundles the exact fixed-coordinate solution used by the
injective code.

The result is still pointwise.  It makes the common coordinate space and the
finite auxiliary ranges explicit, but does not yet choose all point packages
simultaneously or assert a block count.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticFixedBasisEncoding_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- An active large-analytic index carries squarefreeness of its fixed shift. -/
theorem main3LargeAnalytic_shift_squarefree
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Squarefree (shiftedSquareA h v) := by
  have hiActive :=
    (mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi).1
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiActive
  exact (nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
    hiBroad hcell).2.1

/-- Convert a simultaneous package whose frame agrees with `B` into the
fixed-basis encoded-solution type. -/
noncomputable def
    ShiftedSquareSimultaneousNormalizedCoordinatePackage.toEncodedFixedBasisSolution
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (hbasis : P.basis = B.basis) (ht : P.t = B.t) (hc : P.c = B.c) :
    ShiftedSquareEncodedFixedBasisSolution a B.basis B.t B.c where
  C₀ := P.minkowski.C₀
  r := P.r
  ell := P.ell
  x := P.x
  y := P.y
  C₀_pos := P.minkowski.C₀_pos
  solution := by
    simpa only [hbasis, ht, hc] using P.toFixedCoordinateSolution

@[simp]
theorem ShiftedSquareSimultaneousNormalizedCoordinatePackage.code_toEncodedFixedBasisSolution
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (hbasis : P.basis = B.basis) (ht : P.t = B.t) (hc : P.c = B.c) :
    (P.toEncodedFixedBasisSolution B hbasis ht hc).code =
      ⟨P.minkowski.C₀, P.r, P.ell, P.x, P.y⟩ := rfl

/-- The encoded solution obtained from `P` retains the original point
parameters, even though equality transport changes its fixed frame. -/
theorem ShiftedSquareSimultaneousNormalizedCoordinatePackage.toEncodedFixedBasisSolution_originalTriple
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (hbasis : P.basis = B.basis) (ht : P.t = B.t) (hc : P.c = B.c) :
    ((P.toEncodedFixedBasisSolution B hbasis ht hc).solution.d,
        (P.toEncodedFixedBasisSolution B hbasis ht hc).solution.w,
        (P.toEncodedFixedBasisSolution B hbasis ht hc).solution.n) =
      (d, w, n) := by
  let Q : ShiftedSquareFixedCoordinateSolution a B.basis B.t B.c
      P.minkowski.C₀ P.r P.ell P.x P.y := {
    d := d
    w := w
    n := n
    equation := heq
    factorization := by
      rw [← hbasis, ← P.mu_coordinates, ← P.nu_coordinates]
      exact P.minkowski.factorization
    source_norm := by
      simpa only [ht, hc] using P.mu_norm_form
    target_norm := by
      simpa only [ht, hc] using P.nu_norm_form }
  have hsolution :
      (P.toEncodedFixedBasisSolution B hbasis ht hc).solution = Q :=
    shiftedSquareFixedCoordinateSolution_ext P.minkowski.C₀_pos _ _
  exact congrArg (fun R => (R.d, R.w, R.n)) hsolution

/-- The complete same-witness payload for a point represented in the basis
fixed before the point was chosen. -/
structure Main3LargeAnalyticFixedBasisEncodingCertificate
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) where
  P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq
  scaled : Main3LargeAnalyticScaledCoordinateCertificate
    (D := D) (Y := Y) (N := N) heq P
  basis_eq : P.basis = B.basis
  omega_eq : P.omega = B.omega
  t_eq : P.t = B.t
  c_eq : P.c = B.c
  encoded : ShiftedSquareEncodedFixedBasisSolution a B.basis B.t B.c
  encoded_eq : encoded = P.toEncodedFixedBasisSolution B basis_eq t_eq c_eq
  auxiliary_bounds :
    P.minkowski.C₀ ≤ 32 * a.natAbs ∧
      P.r ≤ 64 * a.natAbs ∧
      P.ell ≤ 32 * a.natAbs ∧
      P.bζ.natAbs ≤ 2 ∧
      P.c.natAbs ≤ 4 * a.natAbs + 1

/-- The bundled fixed-coordinate solution is the original `(d,w,n)` point,
not merely another solution with the same shift. -/
theorem Main3LargeAnalyticFixedBasisEncodingCertificate.encoded_originalTriple
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {B : ShiftedSquareFixedExplicitIntegralBasisData a}
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (C : Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq) :
    (C.encoded.solution.d, C.encoded.solution.w,
        C.encoded.solution.n) = (d, w, n) := by
  rw [C.encoded_eq]
  exact C.P.toEncodedFixedBasisSolution_originalTriple
    B C.basis_eq C.t_eq C.c_eq

/-- Its injective code is literally the five scalar/coordinate fields of the
same normalized package. -/
theorem Main3LargeAnalyticFixedBasisEncodingCertificate.encoded_code_eq
    {a : ℤ} {D Y N d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {B : ShiftedSquareFixedExplicitIntegralBasisData a}
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (C : Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq) :
    C.encoded.code =
      ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.x, C.P.y⟩ := by
  rw [C.encoded_eq]
  exact C.P.code_toEncodedFixedBasisSolution B C.basis_eq C.t_eq C.c_eq

/-- Every point of an actual large-analytic block is encoded in one integral
basis chosen solely from the fixed shift and the active-index certificates.
The returned scaled certificate, fixed-frame equalities, encoded solution,
and auxiliary bounds all refer to the same literal package `P`. -/
theorem nonempty_main3LargeAnalytic_fixedBasisEncodingCertificate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N d w n : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : (d, w, n) ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N) :
    let heq := main3LargeAnalytic_squarefreeBlock_equation hp
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    Nonempty (Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq) := by
  let a := shiftedSquareA h v
  let heq := main3LargeAnalytic_squarefreeBlock_equation hp
  let fieldFact : Fact (rationalQuadraticAlgebraNoRationalRoot (-a)) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let ha : Squarefree a := main3LargeAnalytic_shift_squarefree hi
  let B : @ShiftedSquareFixedExplicitIntegralBasisData a fieldFact :=
    @shiftedSquareFixedExplicitIntegralBasisData a fieldFact ha
  change Nonempty (@Main3LargeAnalyticFixedBasisEncodingCertificate
    a D Y N d w n fieldFact B heq)
  have hiActive :=
    (mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi).1
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiActive
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
      hiBroad hcell
  have ha0 : a ≠ 0 := hshift.2.2.1
  obtain ⟨hd, hwpos, hnpos, hDd, hdD, hYw, hwY, hNn, hnN,
      _heq, hw⟩ := mem_squarefreeShiftedSquareBlock.mp hp
  have hwone : 1 < w := by omega
  obtain ⟨P, hbasis, homega, ht, hc⟩ :=
    @exists_shiftedSquareSimultaneousNormalizedCoordinatePackage_usingBasis
      a d w n fieldFact B ha hd hw hwone heq
  have hdominance :=
    mem_main3LargeAnalytic_squarefreeBlock_shift_dominates
      htheta hY hi hp
  let hbase : @Main3LargeAnalyticCoordinateCertificate
      a D Y N d w n fieldFact heq P := {
    source_pos := hd
    target_pos := hwpos
    numerator_pos := hnpos
    source_dyadic := ⟨hDd, hdD⟩
    target_dyadic := ⟨hYw, hwY⟩
    numerator_dyadic := ⟨hNn, hnN⟩
    target_squarefree := hw
    shift_dominance := hdominance
    source_embedding_box := fun place =>
      @shiftedSquare_sourceEmbedding_twoSided
        a d w n fieldFact heq hd P place
    target_embedding_box := fun place =>
      @shiftedSquare_targetEmbedding_twoSided
        a d w n fieldFact heq hd hdominance P place
    source_norm_scale_lower :=
      @shiftedSquare_sourceNormScale_lower a d w n fieldFact heq P
    target_norm_scale_lower :=
      @shiftedSquare_targetNormScale_lower a d w n fieldFact heq P
    fixed_fibre_card_le_one := fun S =>
      @ShiftedSquareSimultaneousNormalizedCoordinatePackage.fixedFiber_card_le_one
        a d w n fieldFact heq P S }
  let hscaled : @Main3LargeAnalyticScaledCoordinateCertificate
      a D Y N d w n fieldFact heq P := {
    base := hbase
    shift_ne_zero := ha0
    surface_coefficient_height :=
      @ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceCoefficientHeight_le
        a d w n fieldFact heq P
    all_surface_coefficients := fun i j =>
      @ShiftedSquareSimultaneousNormalizedCoordinatePackage.surfaceCoefficient_abs_le
        a d w n fieldFact heq P i j
    C₀_le_thirtytwo_mul_sqrt_abs := P.minkowski.C₀_le_thirtytwo_mul_sqrt_abs
    EAlpha_ge_source_floor :=
      @shiftedSquareEAlpha_ge_sourceFloor a d w n fieldFact heq P
    EGamma_ge_target_floor :=
      @shiftedSquareEGamma_ge_targetFloor a d w n fieldFact heq P
    source_embedding_scale_bounds := fun place =>
      @shiftedSquare_sourceEmbedding_scaleBounds
        a d w n fieldFact heq ha0 hd P place
    target_embedding_scale_bounds := fun place =>
      @shiftedSquare_targetEmbedding_scaleBounds
        a d w n fieldFact heq ha0 hd hdominance P place }
  let encoded :=
    @ShiftedSquareSimultaneousNormalizedCoordinatePackage.toEncodedFixedBasisSolution
      a d w n fieldFact B heq P hbasis ht hc
  have haux := @shiftedSquare_auxiliaryParameterBounds
    a d w n fieldFact heq ha0 P
  exact ⟨{
    P := P
    scaled := hscaled
    basis_eq := hbasis
    omega_eq := homega
    t_eq := ht
    c_eq := hc
    encoded := encoded
    encoded_eq := rfl
    auxiliary_bounds := haux }⟩

end

end PellPaper
