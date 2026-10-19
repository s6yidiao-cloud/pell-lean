import Pell.ShiftedSquareEmbeddingScaleBounds
import Pell.ShiftedSquareExplicitIntegralBasisHeight
import Pell.ShiftedSquareFieldDiscriminantLowerBound
import Pell.IntegerSymmetricRectangle
import Mathlib.Tactic

/-!
# Raw integral-coordinate bounds for the shifted-square main3 route

The canonical all-infinite-place estimates control the primitive algebraic
integers, whereas the lattice and cell-counting stages use their two literal
integral-basis coordinates.  This file makes that passage explicit.

For a displayed integral basis `1, omega` with
`omega^2 = t * omega + c`, the two parity branches are encoded by
`t = 0` or `t = 1`.  Field conjugation gives the exact identities

`z + star z = 2 * x 0 + t * x 1`,

`z - star z = x 1 * (omega - star omega)`.

The square of the latter basis difference is the field discriminant.  Its
absolute value is at least `|a|`, so a uniform embedding bound `B` yields

`|x 0| <= 2B`, `|x 1| <= 2B`, and
`|x 1| * sqrt |a| <= 2B`.

Substitution of the canonical embedding-scale loss gives the concrete raw
coordinate loss `1024 * |a|`.  The final theorem records literal membership
in finite integer rectangles; this is a coarse finite-box handoff, not the
later logarithmic/angular cell count.
-/

namespace PellPaper

noncomputable section

local instance main3ShiftedSquareRawCoordinateBounds_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The explicit loss incurred when passing from all-place embedding bounds
to the two raw coordinates in the displayed integral basis. -/
def shiftedSquareRawCoordinateScaleLoss (a : ℤ) : ℝ :=
  1024 * |(a : ℝ)|

private theorem shiftedSquare_displayedOmega_trace
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    Algebra.trace ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) omega = t := by
  have hom : shiftedSquareIntegralBasisElement b ![0, 1] = omega := by
    rw [shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1]
    norm_num
  rw [← hom, Algebra.trace_eq_matrix_trace b,
    shiftedSquareExplicitBasis_leftMulMatrix b omega t c hb0 hb1 homega]
  simp [Matrix.trace, Fin.sum_univ_succ]

/-- The sum of a displayed integral-basis generator and its field conjugate
is exactly the branch parameter `t`.  Thus the half-integral branch
(`t = 1`) is retained rather than silently treated as the standard basis. -/
theorem shiftedSquare_displayedOmega_add_star_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    (omega : rationalQuadraticAlgebra (-a)) +
        star (omega : rationalQuadraticAlgebra (-a)) =
      (t : rationalQuadraticAlgebra (-a)) := by
  have htrace := shiftedSquare_displayedOmega_trace
    b omega t c hb0 hb1 homega
  have htraceCast :
      ((Algebra.trace ℤ
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) omega : ℤ) : ℚ) =
        2 * (omega : rationalQuadraticAlgebra (-a)).re := by
    change (algebraMap ℤ ℚ)
        (Algebra.trace ℤ
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) omega) = _
    rw [← Algebra.intTrace_eq_trace ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))]
    rw [Algebra.algebraMap_intTrace
      (A := ℤ) (K := ℚ)
      (L := rationalQuadraticAlgebra (-a))
      (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))]
    exact rationalQuadraticAlgebra_trace_apply (-a)
      (omega : rationalQuadraticAlgebra (-a))
  rw [htrace] at htraceCast
  have htraceField :
      QuadraticAlgebra.trace (omega : rationalQuadraticAlgebra (-a)) =
        (t : ℚ) := by
    change 2 * (omega : rationalQuadraticAlgebra (-a)).re +
        (0 : ℚ) * (omega : rationalQuadraticAlgebra (-a)).im = (t : ℚ)
    simpa using htraceCast.symm
  rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star]
  rw [htraceField]
  norm_num

/-- The conjugate difference of the displayed integral-basis generator has
square exactly equal to the number-field discriminant. -/
theorem shiftedSquare_displayedOmega_sub_star_sq_eq_fieldDiscr
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    ((omega : rationalQuadraticAlgebra (-a)) -
        star (omega : rationalQuadraticAlgebra (-a))) ^ 2 =
      (NumberField.discr (rationalQuadraticAlgebra (-a)) :
        rationalQuadraticAlgebra (-a)) := by
  have hadd := shiftedSquare_displayedOmega_add_star_eq
    b omega t c hb0 hb1 homega
  have hstar : star (omega : rationalQuadraticAlgebra (-a)) =
      (t : rationalQuadraticAlgebra (-a)) - omega := by
    linear_combination hadd
  have homegaField :
      (omega : rationalQuadraticAlgebra (-a)) ^ 2 =
        (t : rationalQuadraticAlgebra (-a)) * omega + c := by
    exact congrArg Subtype.val homega
  have hdisc := shiftedSquareExplicitIntegralBasis_fieldDiscr
    b omega t c hb0 hb1 homega
  rw [hstar, hdisc]
  push_cast
  linear_combination 4 * homegaField

private theorem shiftedSquare_displayedOmega_sub_star_embedding_norm_sq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma ((omega : rationalQuadraticAlgebra (-a)) -
        star (omega : rationalQuadraticAlgebra (-a)))‖ ^ 2 =
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  rw [← norm_pow, ← map_pow,
    shiftedSquare_displayedOmega_sub_star_sq_eq_fieldDiscr
      b omega t c hb0 hb1 homega,
    map_intCast, Complex.norm_intCast]

/-- Exact inverse-basis trace coordinate: for `z = x 0 + x 1 * omega`,
the conjugate sum is `2 * x 0 + t * x 1`. -/
theorem shiftedSquare_integralBasisElement_add_star_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (x : Fin 2 → ℤ) :
    (shiftedSquareIntegralBasisElement b x : rationalQuadraticAlgebra (-a)) +
        star (shiftedSquareIntegralBasisElement b x :
          rationalQuadraticAlgebra (-a)) =
      ((2 * x 0 + t * x 1 : ℤ) : rationalQuadraticAlgebra (-a)) := by
  have hz :
      (shiftedSquareIntegralBasisElement b x : rationalQuadraticAlgebra (-a)) =
        (x 0 : rationalQuadraticAlgebra (-a)) +
          (x 1 : rationalQuadraticAlgebra (-a)) * omega := by
    exact congrArg Subtype.val
      (shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1 x)
  rw [hz, star_add, star_mul]
  simp only [star_intCast]
  have hadd := shiftedSquare_displayedOmega_add_star_eq
    b omega t c hb0 hb1 homega
  push_cast
  linear_combination (x 1 : rationalQuadraticAlgebra (-a)) * hadd

/-- Exact inverse-basis transverse coordinate: conjugate subtraction isolates
the second raw coordinate without making a choice between `t = 0` and
`t = 1`. -/
theorem shiftedSquare_integralBasisElement_sub_star_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a)))
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (x : Fin 2 → ℤ) :
    (shiftedSquareIntegralBasisElement b x : rationalQuadraticAlgebra (-a)) -
        star (shiftedSquareIntegralBasisElement b x :
          rationalQuadraticAlgebra (-a)) =
      (x 1 : rationalQuadraticAlgebra (-a)) *
        ((omega : rationalQuadraticAlgebra (-a)) -
          star (omega : rationalQuadraticAlgebra (-a))) := by
  have hz :
      (shiftedSquareIntegralBasisElement b x : rationalQuadraticAlgebra (-a)) =
        (x 0 : rationalQuadraticAlgebra (-a)) +
          (x 1 : rationalQuadraticAlgebra (-a)) * omega := by
    exact congrArg Subtype.val
      (shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1 x)
  rw [hz, star_add, star_mul]
  simp only [star_intCast]
  ring

/-- A universal all-infinite-place upper bound gives explicit raw-coordinate
bounds.  The middle estimate is the stronger discriminant-weighted bound;
the last estimate uses `a ≠ 0`, forced by the no-rational-root instance. -/
theorem shiftedSquare_integralCoordinates_bounds_of_all_infinitePlace_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a)
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (ht : t = 0 ∨ t = 1)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (x : Fin 2 → ℤ) (B : ℝ)
    (hupper : ∀ v : NumberField.InfinitePlace
        (rationalQuadraticAlgebra (-a)),
      v (shiftedSquareIntegralBasisElement b x) ≤ B) :
    |(x 0 : ℝ)| ≤ 2 * B ∧
      |(x 1 : ℝ)| ≤ 2 * B ∧
      |(x 1 : ℝ)| * Real.sqrt |(a : ℝ)| ≤ 2 * B := by
  have ha0 : a ≠ 0 := by
    intro ha0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [ha0]
  let sigma : rationalQuadraticAlgebra (-a) →+* ℂ :=
    Classical.choice (inferInstance :
      Nonempty (rationalQuadraticAlgebra (-a) →+* ℂ))
  let z : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement b x
  let delta : rationalQuadraticAlgebra (-a) :=
    (omega : rationalQuadraticAlgebra (-a)) -
      star (omega : rationalQuadraticAlgebra (-a))
  have hz : ‖sigma z‖ ≤ B := by
    simpa only [z, NumberField.InfinitePlace.apply] using
      hupper (NumberField.InfinitePlace.mk sigma)
  have hzstar : ‖sigma (star z)‖ ≤ B := by
    have h := hupper (NumberField.InfinitePlace.mk
      (sigma.comp (starRingEnd (rationalQuadraticAlgebra (-a)))))
    simpa only [z, NumberField.InfinitePlace.apply, RingHom.comp_apply,
      starRingEnd_apply] using h
  have hsubNorm : ‖sigma (z - star z)‖ ≤ 2 * B := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have hsumNorm : ‖sigma (z + star z)‖ ≤ 2 * B := by
    rw [map_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hdeltaSq : ‖sigma delta‖ ^ 2 =
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
    simpa only [delta] using
      shiftedSquare_displayedOmega_sub_star_embedding_norm_sq
        b omega t c hb0 hb1 homega sigma
  have hdiscInt :=
    abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
      a ha
  have hdiscReal : |(a : ℝ)| ≤
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
    exact_mod_cast hdiscInt
  have hdeltaLower : Real.sqrt |(a : ℝ)| ≤ ‖sigma delta‖ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact norm_nonneg _
    · simpa only [hdeltaSq] using hdiscReal
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt |(a : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Int.one_le_abs ha0)
  have hsub := shiftedSquare_integralBasisElement_sub_star_eq
    b omega hb0 hb1 x
  have hx1Product : |(x 1 : ℝ)| * ‖sigma delta‖ ≤ 2 * B := by
    have h := hsubNorm
    rw [show z - star z =
        (x 1 : rationalQuadraticAlgebra (-a)) * delta by
      simpa only [z, delta] using hsub,
      map_mul, norm_mul, map_intCast, Complex.norm_intCast] at h
    exact h
  have hx1Sqrt :
      |(x 1 : ℝ)| * Real.sqrt |(a : ℝ)| ≤ 2 * B :=
    (mul_le_mul_of_nonneg_left hdeltaLower (abs_nonneg _)).trans hx1Product
  have hx1 : |(x 1 : ℝ)| ≤ 2 * B := by
    calc
      |(x 1 : ℝ)| = |(x 1 : ℝ)| * 1 := by ring
      _ ≤ |(x 1 : ℝ)| * Real.sqrt |(a : ℝ)| :=
        mul_le_mul_of_nonneg_left hsqrtOne (abs_nonneg _)
      _ ≤ 2 * B := hx1Sqrt
  have hadd := shiftedSquare_integralBasisElement_add_star_eq
    b omega t c hb0 hb1 homega x
  have hlinear : |((2 * x 0 + t * x 1 : ℤ) : ℝ)| ≤ 2 * B := by
    have h := hsumNorm
    rw [show z + star z =
        ((2 * x 0 + t * x 1 : ℤ) : rationalQuadraticAlgebra (-a)) by
      simpa only [z] using hadd,
      map_intCast, Complex.norm_intCast] at h
    exact h
  have htAbs : |(t : ℝ)| ≤ 1 := by
    rcases ht with rfl | rfl <;> norm_num
  have htx1 : |(t : ℝ) * (x 1 : ℝ)| ≤ 2 * B := by
    rw [abs_mul]
    calc
      |(t : ℝ)| * |(x 1 : ℝ)| ≤ 1 * (2 * B) :=
        mul_le_mul htAbs hx1 (abs_nonneg _) (by norm_num)
      _ = 2 * B := by ring
  have hx0two : 2 * |(x 0 : ℝ)| ≤ 4 * B := by
    calc
      2 * |(x 0 : ℝ)| = |(2 : ℝ) * (x 0 : ℝ)| := by
        rw [abs_mul]
        norm_num
      _ = |(((2 * x 0 + t * x 1 : ℤ) : ℝ) -
          (t : ℝ) * (x 1 : ℝ))| := by
        congr 1
        push_cast
        ring
      _ ≤ |((2 * x 0 + t * x 1 : ℤ) : ℝ)| +
          |(t : ℝ) * (x 1 : ℝ)| := abs_sub _ _
      _ ≤ 2 * B + 2 * B := add_le_add hlinear htx1
      _ = 4 * B := by ring
  exact ⟨by linarith, hx1, hx1Sqrt⟩

/-- The primitive source coordinates are uniformly bounded by the concrete
polynomial loss times `sqrt E_alpha`, with an additional transverse
`sqrt |a|` gain for coordinate `1`. -/
theorem shiftedSquare_sourceRawCoordinates_scaleBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    |(P.x 0 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
        Real.sqrt (shiftedSquareEAlpha P) ∧
      |(P.x 1 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
        Real.sqrt (shiftedSquareEAlpha P) ∧
      |(P.x 1 : ℝ)| * Real.sqrt |(a : ℝ)| ≤
        shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEAlpha P) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [ha0]
  have h := shiftedSquare_integralCoordinates_bounds_of_all_infinitePlace_le
    ha P.basis P.omega P.t P.c P.basis_zero P.basis_one
      P.t_zero_or_one P.omega_sq P.x
      (shiftedSquareEmbeddingScaleLoss a *
        Real.sqrt (shiftedSquareEAlpha P))
      (fun v => (shiftedSquare_sourceEmbedding_scaleBounds ha0 hd P v).2)
  have hloss : 2 * shiftedSquareEmbeddingScaleLoss a =
      shiftedSquareRawCoordinateScaleLoss a := by
    simp only [shiftedSquareEmbeddingScaleLoss,
      shiftedSquareRawCoordinateScaleLoss]
    ring
  rw [← mul_assoc, hloss] at h
  exact h

/-- On the large shifted-square range, the primitive target coordinates obey
the same concrete raw-coordinate loss at scale `sqrt E_gamma`. -/
theorem shiftedSquare_targetRawCoordinates_scaleBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    |(P.y 0 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
        Real.sqrt (shiftedSquareEGamma P) ∧
      |(P.y 1 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
        Real.sqrt (shiftedSquareEGamma P) ∧
      |(P.y 1 : ℝ)| * Real.sqrt |(a : ℝ)| ≤
        shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEGamma P) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [ha0]
  have h := shiftedSquare_integralCoordinates_bounds_of_all_infinitePlace_le
    ha P.basis P.omega P.t P.c P.basis_zero P.basis_one
      P.t_zero_or_one P.omega_sq P.y
      (shiftedSquareEmbeddingScaleLoss a *
        Real.sqrt (shiftedSquareEGamma P))
      (fun v => (shiftedSquare_targetEmbedding_scaleBounds ha0 hd hn P v).2)
  have hloss : 2 * shiftedSquareEmbeddingScaleLoss a =
      shiftedSquareRawCoordinateScaleLoss a := by
    simp only [shiftedSquareEmbeddingScaleLoss,
      shiftedSquareRawCoordinateScaleLoss]
    ring
  rw [← mul_assoc, hloss] at h
  exact h

/-- Simultaneous explicit raw bounds for all four primitive integral
coordinates used by the main3 lattice route. -/
theorem shiftedSquare_primitiveRawCoordinates_scaleBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (|(P.x 0 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEAlpha P) ∧
        |(P.x 1 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEAlpha P)) ∧
      (|(P.y 0 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEGamma P) ∧
        |(P.y 1 : ℝ)| ≤ shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEGamma P)) := by
  have hx := shiftedSquare_sourceRawCoordinates_scaleBounds ha hd P
  have hy := shiftedSquare_targetRawCoordinates_scaleBounds ha hd hn P
  exact ⟨⟨hx.1, hx.2.1⟩, ⟨hy.1, hy.2.1⟩⟩

/-- The four raw coordinate inequalities are literal membership in a product
of two finite symmetric integer rectangles. -/
theorem shiftedSquare_primitiveRawCoordinates_mem_scaleRectangles
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    P.x ∈ integerSymmetricRectangle
        (shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEAlpha P))
        (shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEAlpha P)) ∧
      P.y ∈ integerSymmetricRectangle
        (shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEGamma P))
        (shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEGamma P)) := by
  have h := shiftedSquare_primitiveRawCoordinates_scaleBounds ha hd hn P
  constructor
  · rw [mem_integerSymmetricRectangle]
    exact h.1
  · rw [mem_integerSymmetricRectangle]
    exact h.2

end

end PellPaper
